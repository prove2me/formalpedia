-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd
-- name    : AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/bbcf81e6-7b88-5d04-8bf2-2391246ed408
-- title:
--   Properness descends to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a Noetherian commutative ring, let $A$ be a commutative $A_0$-algebra, and let $f \colon X \to \operatorname{Spec} A_0$ be a morphism of schemes which is separated, quasi-compact and locally of finite type. Assume that the second projection of the fibre product of $f$ with $\operatorname{Spec}$ of the structure map $A_0 \to A$, that is the base change $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A \to \operatorname{Spec} A$, is proper. Then for every finite subset $s \subseteq A$ there exists an $A_0$-subalgebra $T \subseteq A$ such that $T$ is finitely generated as an $A_0$-algebra, $s$ is contained in $T$, and the second projection of the fibre product of $f$ with $\operatorname{Spec}$ of the structure map $A_0 \to T$, that is the base change $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} T \to \operatorname{Spec} T$, is again proper. All schemes and rings live in a single universe.
--
--   This is the descent of properness along a directed union of subalgebras, a case of the limit formalism of EGA IV, §8 (8.10.5): a property of the base change to $A$, which is the filtered colimit of its finitely generated $A_0$-subalgebras, already holds at some finitely generated stage, and the finite set $s$ allows one to prescribe finitely many elements of that stage. It is used in the project to spread out proper (and flat, smooth, or abelian-scheme) situations over a finitely generated base, for instance in [`AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation), [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected) and in the construction of good-reduction models of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) := by sorry
