-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
-- name    : AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/bcdd1578-85f4-56b5-988e-0c32bd149c40
-- title:
--   Smoothness after base change descends to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ a commutative $A_0$-algebra, let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} A_0$ be a morphism which is quasi-compact and locally of finite presentation. Assume that the second projection of the fibre product of $f$ with the morphism $\operatorname{Spec} A \to \operatorname{Spec} A_0$ induced by the structure map $A_0 \to A$, that is the base change $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A \to \operatorname{Spec} A$, is smooth. Then for every finite subset $s$ of $A$ there exists an $A_0$-subalgebra $T$ of $A$ which is finitely generated as an $A_0$-algebra, contains $s$, and is such that the second projection of the fibre product of $f$ with $\operatorname{Spec} T \to \operatorname{Spec} A_0$ induced by $A_0 \to T$, namely $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} T \to \operatorname{Spec} T$, is again smooth. All rings, the scheme $X$ and the subalgebra $T$ live in a single universe.
--
--   This is the descent of smoothness along the filtered system of finitely generated $A_0$-subalgebras of $A$ (EGA IV 17.7.8): a property that holds after base change to the limit $A$ already holds at some finite stage, with the stage chosen large enough to contain a prescribed finite set of elements. It is the smoothness member of the Noetherian-approximation package, and is used in the construction of finitely generated bases over which a given pullback square remains smooth, proper and geometrically connected, in the openness of the locus of irreducible fibres, and in the approximation of abelian-scheme data for Jacobians of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by sorry
