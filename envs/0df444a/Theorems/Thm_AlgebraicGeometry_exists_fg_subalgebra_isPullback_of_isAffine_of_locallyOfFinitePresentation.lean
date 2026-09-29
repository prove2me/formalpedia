-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a3459f42-a9dc-5d8b-b119-44ffc98c1664
-- title:
--   Affine model over a finitely generated subalgebra
-- statement:
--   Let $A_0$, $R$, $A$ be commutative rings in a fixed universe, with $A_0$-algebra structures on $R$ and on $A$ and an $R$-algebra structure on $A$ forming a scalar tower, and assume $R$ is of finite type over $A_0$. Let $X$ be an affine scheme and $g \colon X \to \operatorname{Spec} A$ a morphism locally of finite presentation, and let $s$ be a finite subset of $A$. The assertion is that there exists an $A_0$-subalgebra $T \subseteq A$ which is finitely generated, contains $s$ and contains the image of the structure map $R \to A$, together with a scheme $X_0$, a morphism $f_0 \colon X_0 \to \operatorname{Spec} T$ and a morphism $\pi \colon X \to X_0$, such that $X_0$ is affine, $f_0$ is locally of finite presentation, quasi-compact and quasi-separated, and the square formed by $\pi$, $g$, $f_0$ and the morphism $\operatorname{Spec} A \to \operatorname{Spec} T$ induced by the inclusion $T \hookrightarrow A$ is cartesian, exhibiting $X \cong X_0 \times_{\operatorname{Spec} T} \operatorname{Spec} A$.
--
--   This is the affine case of the standard descent of a finitely presented morphism to a finite-type stage of the directed system of finitely generated subalgebras of the base (EGA IV₃ 8.8.2), with the extra feature that the chosen stage may be required to contain a prescribed finite set and the image of an intermediate finite-type ring $R$. It is the base case for the general statement [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation), and the ring-theoretic input is [`Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`](thm.html#Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit), which produces a finitely presented algebra over some stage whose base change recovers the given one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
    {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A] [Algebra A₀ A]
    [IsScalarTower A₀ R A] [Algebra.FiniteType A₀ R]
    {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsAffine X₀ ∧ LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
        IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by sorry
