-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem
-- name    : AlgebraicGeometry.Scheme.range_subset_of_isLocalRing_of_closedPoint_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/186020a6-8db9-592c-bcf3-e463ae64513b
-- title:
--   Image of Spec of a local ring lies in any open containing the closed point
-- statement:
--   Let $X$ be a scheme, $U$ an open subscheme of $X$ (an element of `X.Opens`, i.e. an open subset of the underlying space), and $T$ a commutative ring that is a local ring. Let $f : \operatorname{Spec}(T) \to X$ be a morphism of schemes, where $\operatorname{Spec}(T)$ is the spectrum of $T$ viewed as an object of `CommRingCat`, and suppose the image under the underlying continuous map `f.base` of the closed point of $\operatorname{Spec}(T)$ — the point corresponding to the maximal ideal of $T$, given by `IsLocalRing.closedPoint T` — lies in $U$. The conclusion is that the whole set-theoretic range of `f.base` is contained in $U$, regarded as a subset of the underlying topological space of $X$. Thus a morphism from the spectrum of a local ring to $X$ whose closed point maps into $U$ has its entire image inside $U$; this is a statement about underlying spaces only, and no factorisation of $f$ through $U$ is asserted here.
--
--   This is the standard topological observation underlying the fact that a morphism from the spectrum of a local ring factors through any open neighbourhood of the image of the closed point. It is used in the project to produce factorisations through open immersions, in [`AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion`](thm.html#AlgebraicGeometry.Scheme.forall_exists_algHom_lift_of_forall_exists_lift_of_isOpenImmersion) and its algebraically closed variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.range_subset_of_isLocalRing_of_closedPoint_mem
    {X : Scheme.{u}} (U : X.Opens) (T : Type u) [CommRing T] [IsLocalRing T]
    (f : Spec (CommRingCat.of T) ⟶ X) (hx : f.base (IsLocalRing.closedPoint T) ∈ U) :
    Set.range f.base ⊆ (U : Set ↥X) := by sorry
