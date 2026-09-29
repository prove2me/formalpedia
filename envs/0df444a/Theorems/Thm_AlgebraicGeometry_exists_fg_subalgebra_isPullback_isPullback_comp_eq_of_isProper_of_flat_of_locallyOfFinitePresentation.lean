-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/879b2695-d4e4-51fe-bcdd-32d156f27207
-- title:
--   Descent of a morphism of proper flat schemes to a f.g. subalgebra
-- statement:
--   Let $A$ be a commutative ring and let $Z$, $X$ be schemes (all in the base universe), with morphisms $p : Z \to \operatorname{Spec} A$, $q : X \to \operatorname{Spec} A$ and $h : Z \to X$ satisfying $q \circ h = p$, and assume that both $p$ and $q$ are proper, flat and locally of finite presentation. The assertion is that there exists a subalgebra $T \subseteq A$ over $\mathbb{Z}$ which is finitely generated (as a $\mathbb{Z}$-algebra), together with schemes $Z_0$, $X_0$, morphisms $p_0 : Z_0 \to \operatorname{Spec} T$, $q_0 : X_0 \to \operatorname{Spec} T$ and $h_0 : Z_0 \to X_0$, and morphisms $\pi_Z : Z \to Z_0$, $\pi_X : X \to X_0$, such that: $q_0 \circ h_0 = p_0$; each of $p_0$ and $q_0$ is proper, flat and locally of finite presentation; the square formed by $\pi_Z$, $p$, $p_0$ and $\operatorname{Spec}$ of the inclusion $T \to A$ is cartesian, and likewise the square formed by $\pi_X$, $q$, $q_0$ and $\operatorname{Spec}(T \to A)$; and $\pi_X \circ h = h_0$ followed by nothing further, i.e. $h$ followed by $\pi_X$ equals $\pi_Z$ followed by $h_0$. Thus $Z$, $X$ and $h$ are obtained from $Z_0$, $X_0$ and $h_0$ by base change along $\operatorname{Spec} A \to \operatorname{Spec} T$.
--
--   This is the noetherian approximation (spreading out) step of EGA IV§8 in the form needed for a pair of proper flat finitely presented schemes over an affine base together with a morphism between them: everything descends to a finitely generated, hence noetherian, $\mathbb{Z}$-subalgebra of the base ring. It is used in the proof of [`AlgebraicGeometry.isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat`](thm.html#AlgebraicGeometry.isCompact_inter_setOf_isIso_fibre_of_isAffineOpen_of_isProper_of_flat), where a noetherian base is required; the proof combines the descent of a single proper flat finitely presented scheme with the descent of a morphism into a scheme locally of finite presentation, after enlarging the subalgebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_isPullback_comp_eq_of_isProper_of_flat_of_locallyOfFinitePresentation
    {A : Type} [CommRing A] {X Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of A)) (q : X ⟶ Spec (CommRingCat.of A)) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q] :
    ∃ (T : Subalgebra ℤ A), T.FG ∧
      ∃ (Z₀ X₀ : Scheme.{0}) (p₀ : Z₀ ⟶ Spec (CommRingCat.of ↥T)) (q₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (h₀ : Z₀ ⟶ X₀)
        (πZ : Z ⟶ Z₀) (πX : X ⟶ X₀),
        h₀ ≫ q₀ = p₀ ∧ IsProper p₀ ∧ Flat p₀ ∧ LocallyOfFinitePresentation p₀ ∧
        IsProper q₀ ∧ Flat q₀ ∧ LocallyOfFinitePresentation q₀ ∧
        IsPullback πZ p p₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        IsPullback πX q q₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) ∧
        h ≫ πX = πZ ≫ h₀ := by sorry
