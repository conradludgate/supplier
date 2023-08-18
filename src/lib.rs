//! Supply values dynamically.
//!
//! API is very unstable. It will likely include a breaking change with any patch version.
//!
//! This is intended to replace the `Provider` API that was proposed for the core rust library,
//! but has been decided to not include.
use core::any::TypeId;
use core::fmt;

/// Trait implemented by a type which can dynamically provide values based on type.
pub trait Provider {
    /// Data providers should implement this method to provide *all* values they are able to
    /// provide by using `demand`.
    ///
    /// Note that the `provide_*` methods on `Demand` have short-circuit semantics: if an earlier
    /// method has successfully provided a value, then later methods will not get an opportunity to
    /// provide.
    ///
    /// # Examples
    ///
    /// Provides a reference to a field with type `String` as a `&str`, and a value of
    /// type `i32`.
    ///
    /// ```rust
    /// # #![feature(provide_any)]
    /// use std::any::{Provider, Demand};
    /// # struct SomeConcreteType { field: String, num_field: i32 }
    ///
    /// impl Provider for SomeConcreteType {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         demand.provide_ref::<str>(&self.field)
    ///             .provide_value::<i32>(self.num_field);
    ///     }
    /// }
    /// ```
    fn provide<'a>(&'a self, demand: &mut Demand<'a>);
}

/// Request a value from the `Provider`.
///
/// # Examples
///
/// Get a string value from a provider.
///
/// ```rust
/// # #![feature(provide_any)]
/// use std::any::{Provider, request_value};
///
/// fn get_string(provider: &impl Provider) -> String {
///     request_value::<String>(provider).unwrap()
/// }
/// ```
pub fn request_value<'a, T>(provider: &'a (impl Provider + ?Sized)) -> Option<T>
where
    T: 'static,
{
    request_by_type_tag::<'a, tags::Value<T>>(provider)
}

/// Request a reference from the `Provider`.
///
/// # Examples
///
/// Get a string reference from a provider.
///
/// ```rust
/// # #![feature(provide_any)]
/// use std::any::{Provider, request_ref};
///
/// fn get_str(provider: &impl Provider) -> &str {
///     request_ref::<str>(provider).unwrap()
/// }
/// ```
pub fn request_ref<'a, T>(provider: &'a (impl Provider + ?Sized)) -> Option<&'a T>
where
    T: 'static + ?Sized,
{
    request_by_type_tag::<'a, tags::Ref<tags::MaybeSizedValue<T>>>(provider)
}

/// Request a specific value by tag from the `Provider`.
fn request_by_type_tag<'a, I>(provider: &'a (impl Provider + ?Sized)) -> Option<I::Reified>
where
    I: tags::Type<'a>,
{
    let mut tagged = TaggedOption::<'a, I>(None);
    provider.provide(tagged.as_demand());
    tagged.0
}

///////////////////////////////////////////////////////////////////////////////
// Demand and its methods
///////////////////////////////////////////////////////////////////////////////

/// A helper object for providing data by type.
///
/// A data provider provides values by calling this type's provide methods.
#[cfg_attr(not(doc), repr(transparent))] // work around https://github.com/rust-lang/rust/issues/90435
pub struct Demand<'a>(dyn Erased<'a> + 'a);

impl<'a> Demand<'a> {
    /// Create a new `&mut Demand` from a `&mut dyn Erased` trait object.
    fn new<'b>(erased: &'b mut (dyn Erased<'a> + 'a)) -> &'b mut Demand<'a> {
        // SAFETY: transmuting `&mut (dyn Erased<'a> + 'a)` to `&mut Demand<'a>` is safe since
        // `Demand` is repr(transparent).
        unsafe { &mut *(erased as *mut dyn Erased<'a> as *mut Demand<'a>) }
    }

    /// Provide a value or other type with only static lifetimes.
    ///
    /// # Examples
    ///
    /// Provides an `u8`.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    /// # struct SomeConcreteType { field: u8 }
    ///
    /// impl Provider for SomeConcreteType {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         demand.provide_value::<u8>(self.field);
    ///     }
    /// }
    /// ```
    pub fn provide_value<T>(&mut self, value: T) -> &mut Self
    where
        T: 'static,
    {
        self.provide::<tags::Value<T>>(value)
    }

    /// Provide a value or other type with only static lifetimes computed using a closure.
    ///
    /// # Examples
    ///
    /// Provides a `String` by cloning.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    /// # struct SomeConcreteType { field: String }
    ///
    /// impl Provider for SomeConcreteType {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         demand.provide_value_with::<String>(|| self.field.clone());
    ///     }
    /// }
    /// ```
    pub fn provide_value_with<T>(&mut self, fulfil: impl FnOnce() -> T) -> &mut Self
    where
        T: 'static,
    {
        self.provide_with::<tags::Value<T>>(fulfil)
    }

    /// Provide a reference. The referee type must be bounded by `'static`,
    /// but may be unsized.
    ///
    /// # Examples
    ///
    /// Provides a reference to a field as a `&str`.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    /// # struct SomeConcreteType { field: String }
    ///
    /// impl Provider for SomeConcreteType {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         demand.provide_ref::<str>(&self.field);
    ///     }
    /// }
    /// ```
    pub fn provide_ref<T: ?Sized + 'static>(&mut self, value: &'a T) -> &mut Self {
        self.provide::<tags::Ref<tags::MaybeSizedValue<T>>>(value)
    }

    /// Provide a reference computed using a closure. The referee type
    /// must be bounded by `'static`, but may be unsized.
    ///
    /// # Examples
    ///
    /// Provides a reference to a field as a `&str`.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    /// # struct SomeConcreteType { business: String, party: String }
    /// # fn today_is_a_weekday() -> bool { true }
    ///
    /// impl Provider for SomeConcreteType {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         demand.provide_ref_with::<str>(|| {
    ///             if today_is_a_weekday() {
    ///                 &self.business
    ///             } else {
    ///                 &self.party
    ///             }
    ///         });
    ///     }
    /// }
    /// ```
    pub fn provide_ref_with<T: ?Sized + 'static>(
        &mut self,
        fulfil: impl FnOnce() -> &'a T,
    ) -> &mut Self {
        self.provide_with::<tags::Ref<tags::MaybeSizedValue<T>>>(fulfil)
    }

    /// Provide a value with the given `Type` tag.
    fn provide<I>(&mut self, value: I::Reified) -> &mut Self
    where
        I: tags::Type<'a>,
    {
        if let Some(res @ TaggedOption(None)) = self.0.downcast_mut::<I>() {
            res.0 = Some(value);
        }
        self
    }

    /// Provide a value with the given `Type` tag, using a closure to prevent unnecessary work.
    fn provide_with<I>(&mut self, fulfil: impl FnOnce() -> I::Reified) -> &mut Self
    where
        I: tags::Type<'a>,
    {
        if let Some(res @ TaggedOption(None)) = self.0.downcast_mut::<I>() {
            res.0 = Some(fulfil());
        }
        self
    }

    /// Check if the `Demand` would be satisfied if provided with a
    /// value of the specified type. If the type does not match or has
    /// already been provided, returns false.
    ///
    /// # Examples
    ///
    /// Check if an `u8` still needs to be provided and then provides
    /// it.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    ///
    /// struct Parent(Option<u8>);
    ///
    /// impl Provider for Parent {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         if let Some(v) = self.0 {
    ///             demand.provide_value::<u8>(v);
    ///         }
    ///     }
    /// }
    ///
    /// struct Child {
    ///     parent: Parent,
    /// }
    ///
    /// impl Child {
    ///     // Pretend that this takes a lot of resources to evaluate.
    ///     fn an_expensive_computation(&self) -> Option<u8> {
    ///         Some(99)
    ///     }
    /// }
    ///
    /// impl Provider for Child {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         // In general, we don't know if this call will provide
    ///         // an `u8` value or not...
    ///         self.parent.provide(demand);
    ///
    ///         // ...so we check to see if the `u8` is needed before
    ///         // we run our expensive computation.
    ///         if demand.would_be_satisfied_by_value_of::<u8>() {
    ///             if let Some(v) = self.an_expensive_computation() {
    ///                 demand.provide_value::<u8>(v);
    ///             }
    ///         }
    ///
    ///         // The demand will be satisfied now, regardless of if
    ///         // the parent provided the value or we did.
    ///         assert!(!demand.would_be_satisfied_by_value_of::<u8>());
    ///     }
    /// }
    ///
    /// let parent = Parent(Some(42));
    /// let child = Child { parent };
    /// assert_eq!(Some(42), std::any::request_value::<u8>(&child));
    ///
    /// let parent = Parent(None);
    /// let child = Child { parent };
    /// assert_eq!(Some(99), std::any::request_value::<u8>(&child));
    /// ```
    pub fn would_be_satisfied_by_value_of<T>(&self) -> bool
    where
        T: 'static,
    {
        self.would_be_satisfied_by::<tags::Value<T>>()
    }

    /// Check if the `Demand` would be satisfied if provided with a
    /// reference to a value of the specified type. If the type does
    /// not match or has already been provided, returns false.
    ///
    /// # Examples
    ///
    /// Check if a `&str` still needs to be provided and then provides
    /// it.
    ///
    /// ```rust
    /// #![feature(provide_any)]
    ///
    /// use std::any::{Provider, Demand};
    ///
    /// struct Parent(Option<String>);
    ///
    /// impl Provider for Parent {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         if let Some(v) = &self.0 {
    ///             demand.provide_ref::<str>(v);
    ///         }
    ///     }
    /// }
    ///
    /// struct Child {
    ///     parent: Parent,
    ///     name: String,
    /// }
    ///
    /// impl Child {
    ///     // Pretend that this takes a lot of resources to evaluate.
    ///     fn an_expensive_computation(&self) -> Option<&str> {
    ///         Some(&self.name)
    ///     }
    /// }
    ///
    /// impl Provider for Child {
    ///     fn provide<'a>(&'a self, demand: &mut Demand<'a>) {
    ///         // In general, we don't know if this call will provide
    ///         // a `str` reference or not...
    ///         self.parent.provide(demand);
    ///
    ///         // ...so we check to see if the `&str` is needed before
    ///         // we run our expensive computation.
    ///         if demand.would_be_satisfied_by_ref_of::<str>() {
    ///             if let Some(v) = self.an_expensive_computation() {
    ///                 demand.provide_ref::<str>(v);
    ///             }
    ///         }
    ///
    ///         // The demand will be satisfied now, regardless of if
    ///         // the parent provided the reference or we did.
    ///         assert!(!demand.would_be_satisfied_by_ref_of::<str>());
    ///     }
    /// }
    ///
    /// let parent = Parent(Some("parent".into()));
    /// let child = Child { parent, name: "child".into() };
    /// assert_eq!(Some("parent"), std::any::request_ref::<str>(&child));
    ///
    /// let parent = Parent(None);
    /// let child = Child { parent, name: "child".into() };
    /// assert_eq!(Some("child"), std::any::request_ref::<str>(&child));
    /// ```
    pub fn would_be_satisfied_by_ref_of<T>(&self) -> bool
    where
        T: ?Sized + 'static,
    {
        self.would_be_satisfied_by::<tags::Ref<tags::MaybeSizedValue<T>>>()
    }

    fn would_be_satisfied_by<I>(&self) -> bool
    where
        I: tags::Type<'a>,
    {
        matches!(self.0.downcast::<I>(), Some(TaggedOption(None)))
    }
}
impl<'a> fmt::Debug for Demand<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Demand").finish_non_exhaustive()
    }
}
///////////////////////////////////////////////////////////////////////////////
// Type tags
///////////////////////////////////////////////////////////////////////////////

mod tags {
    //! Type tags are used to identify a type using a separate value. This module includes type tags
    //! for some very common types.
    //!
    //! Currently type tags are not exposed to the user. But in the future, if you want to use the
    //! Provider API with more complex types (typically those including lifetime parameters), you
    //! will need to write your own tags.

    use core::marker::PhantomData;

    /// This trait is implemented by specific tag types in order to allow
    /// describing a type which can be requested for a given lifetime `'a`.
    ///
    /// A few example implementations for type-driven tags can be found in this
    /// module, although crates may also implement their own tags for more
    /// complex types with internal lifetimes.
    pub trait Type<'a>: Sized + 'static {
        /// The type of values which may be tagged by this tag for the given
        /// lifetime.
        type Reified: 'a;
    }

    /// Similar to the [`Type`] trait, but represents a type which may be unsized (i.e., has a
    /// `?Sized` bound). E.g., `str`.
    pub trait MaybeSizedType<'a>: Sized + 'static {
        type Reified: 'a + ?Sized;
    }

    impl<'a, T: Type<'a>> MaybeSizedType<'a> for T {
        type Reified = T::Reified;
    }

    /// Type-based tag for types bounded by `'static`, i.e., with no borrowed elements.
    #[derive(Debug)]
    pub struct Value<T: 'static>(PhantomData<T>);

    impl<'a, T: 'static> Type<'a> for Value<T> {
        type Reified = T;
    }

    /// Type-based tag similar to [`Value`] but which may be unsized (i.e., has a `?Sized` bound).
    #[derive(Debug)]
    pub struct MaybeSizedValue<T: ?Sized + 'static>(PhantomData<T>);

    impl<'a, T: ?Sized + 'static> MaybeSizedType<'a> for MaybeSizedValue<T> {
        type Reified = T;
    }

    /// Type-based tag for reference types (`&'a T`, where T is represented by
    /// `<I as MaybeSizedType<'a>>::Reified`.
    #[derive(Debug)]
    pub struct Ref<I>(PhantomData<I>);

    impl<'a, I: MaybeSizedType<'a>> Type<'a> for Ref<I> {
        type Reified = &'a I::Reified;
    }
}

/// An `Option` with a type tag `I`.
///
/// Since this struct implements `Erased`, the type can be erased to make a dynamically typed
/// option. The type can be checked dynamically using `Erased::tag_id` and since this is statically
/// checked for the concrete type, there is some degree of type safety.
#[repr(transparent)]
struct TaggedOption<'a, I: tags::Type<'a>>(Option<I::Reified>);

impl<'a, I: tags::Type<'a>> TaggedOption<'a, I> {
    fn as_demand(&mut self) -> &mut Demand<'a> {
        Demand::new(self as &mut (dyn Erased<'a> + 'a))
    }
}

/// Represents a type-erased but identifiable object.
///
/// This trait is exclusively implemented by the `TaggedOption` type.
unsafe trait Erased<'a>: 'a {
    /// The `TypeId` of the erased type.
    fn tag_id(&self) -> TypeId;
}

unsafe impl<'a, I: tags::Type<'a>> Erased<'a> for TaggedOption<'a, I> {
    fn tag_id(&self) -> TypeId {
        TypeId::of::<I>()
    }
}

impl<'a> dyn Erased<'a> + 'a {
    /// Returns some reference to the dynamic value if it is tagged with `I`,
    /// or `None` otherwise.
    #[inline]
    fn downcast<I>(&self) -> Option<&TaggedOption<'a, I>>
    where
        I: tags::Type<'a>,
    {
        if self.tag_id() == TypeId::of::<I>() {
            // SAFETY: Just checked whether we're pointing to an I.
            Some(unsafe { &*(self as *const Self).cast::<TaggedOption<'a, I>>() })
        } else {
            None
        }
    }

    /// Returns some mutable reference to the dynamic value if it is tagged with `I`,
    /// or `None` otherwise.
    #[inline]
    fn downcast_mut<I>(&mut self) -> Option<&mut TaggedOption<'a, I>>
    where
        I: tags::Type<'a>,
    {
        if self.tag_id() == TypeId::of::<I>() {
            // SAFETY: Just checked whether we're pointing to an I.
            Some(unsafe { &mut *(self as *mut Self).cast::<TaggedOption<'a, I>>() })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Provider, request_ref};

    struct Container {
        x: u8,
        y: String,
        z: Vec<u8>,
    }

    impl Provider for Container {
        fn provide<'a>(&'a self, demand: &mut crate::Demand<'a>) {
            demand
                .provide_ref(&self.x)
                .provide_ref(&*self.y)
                .provide_ref(&*self.z);
        }
    }

    #[test]
    fn it_works() {
        let c = Container {
            x: 42,
            y: "foobar".to_string(),
            z: vec![1, 2, 3],
        };

        assert_eq!(request_ref::<u8>(&c).unwrap(), &42);
        assert_eq!(request_ref::<str>(&c).unwrap(), "foobar");
        assert_eq!(request_ref::<[u8]>(&c).unwrap(), &[1, 2, 3]);
    }
}
