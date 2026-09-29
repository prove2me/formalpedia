-- Prove2me | Theorems.Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd
-- name    : AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/901a5442-caf6-5aeb-8b03-595de49da418
-- title:
--   Flatness descends to a finitely generated subalgebra stage
-- statement:
--   Let $A_0$ and $A$ be commutative rings in a fixed universe with $A$ an $A_0$-algebra, and let $f\colon X\to\operatorname{Spec}A_0$ be a morphism of schemes that is quasi-compact and locally of finite presentation. Write $\operatorname{Spec}A\to\operatorname{Spec}A_0$ for the morphism induced by the structure map $A_0\to A$, and assume that the second projection of the pullback of $f$ along it, i.e. the base-changed morphism $X\times_{\operatorname{Spec}A_0}\operatorname{Spec}A\to\operatorname{Spec}A$, is flat. Then for every finite subset $s$ of $A$ there exists an $A_0$-subalgebra $T\subseteq A$ which is finitely generated as an $A_0$-algebra, contains $s$ as a subset of $A$, and is such that the second projection of the pullback of $f$ along the morphism $\operatorname{Spec}T\to\operatorname{Spec}A_0$, i.e. $X\times_{\operatorname{Spec}A_0}\operatorname{Spec}T\to\operatorname{Spec}T$, is again flat. Flatness here is the Mathlib morphism property of schemes, and finite generation is expressed as the `FG` predicate on subalgebras.
--
--   This is the scheme-level descent of flatness to a finitely generated stage in a filtered union of subalgebras, in the style of EGA IV 11.2.6. It feeds the construction of a finitely generated base over which a proper flat pullback square is realised, used to spread out proper flat morphisms in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [LocallyOfFinitePresentation f]
    [Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Flat (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by sorry
