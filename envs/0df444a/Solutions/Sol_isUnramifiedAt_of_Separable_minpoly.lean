-- Prove2me | solution 1 for isUnramifiedAt_of_Separable_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:51.686928+00:00
-- url     : https://prove2.me/submissions/01df0209-fb98-41ab-8f29-f789983cc6eb

module
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Unramified.Locus
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Theorems.Thm_P2M_isUnramifiedAt_of_Separable_minpoly__f9724c9343b9

set_option autoImplicit false
@[expose] public section
public section
open UniqueFactorizationMonoid Ideal
attribute [local instance] FractionRing.liftAlgebra
variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]
variable {R} {S}
open nonZeroDivisors Polynomial
theorem _root_.solution [Algebra.IsSeparable K L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥) (x : L) (hx : IsIntegral R x)
    (hx' : Algebra.adjoin K {x} = ⊤)
    (h : Polynomial.Separable ((minpoly R x).map (Ideal.Quotient.mk (P.under R)))) :
    Algebra.IsUnramifiedAt R P := by
  rw [← IsIntegralClosure.algebraMap_mk' S x hx, minpoly.algebraMap_eq
    (IsIntegralClosure.algebraMap_injective S R L)] at h
  exact isUnramifiedAt_of_Separable_minpoly' K L P hPbot (IsIntegralClosure.mk' S x hx)
    (by rwa [IsIntegralClosure.algebraMap_mk']) h
