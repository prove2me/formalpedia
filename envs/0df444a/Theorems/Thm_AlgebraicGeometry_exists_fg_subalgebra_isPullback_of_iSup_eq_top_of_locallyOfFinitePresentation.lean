-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3d85fc19-255b-574a-88e0-7478571ecbc4
-- title:
--   Gluing two quasi-compact opens that descend to finite stages
-- statement:
--   Let $A_0 \to R \to A$ be a tower of commutative rings (all in one universe), with compatible algebra structures and with $R$ of finite type as an $A_0$-algebra. Let $X$ be a scheme and $g \colon X \to \operatorname{Spec} A$ a quasi-compact, quasi-separated morphism locally of finite presentation, and let $U, V$ be open subschemes of $X$ with $U \sqcup V = \top$ (so $U$ and $V$ cover $X$) whose underlying sets are compact. Assume that $U$ descends to arbitrarily large finite stages: for every finite subset $SS'$ of $A$ there are a finitely generated $A_0$-subalgebra $T \subseteq A$ containing $SS'$ and the whole image of $A$ under $\operatorname{algebraMap} R A$, a scheme $X_0$, a morphism $f_0 \colon X_0 \to \operatorname{Spec} T$ that is locally of finite presentation, quasi-compact and quasi-separated, and a morphism $\pi$ from $U$ to $X_0$ making the square formed by $\pi$, the composite $U \hookrightarrow X \xrightarrow{g} \operatorname{Spec} A$, $f_0$ and $\operatorname{Spec}(T \to A)$ a pullback square; assume the same for $V$. Then, for a given finite subset $SS$ of $A$, the identical conclusion holds for $X$ itself: there exist a finitely generated $A_0$-subalgebra $T \subseteq A$ containing $SS$ and the image of $R$ in $A$, and a quasi-compact, quasi-separated morphism $f_0 \colon X_0 \to \operatorname{Spec} T$ locally of finite presentation together with $\pi \colon X \to X_0$ exhibiting $g$ as the base change of $f_0$ along $\operatorname{Spec}(T \to A)$.
--
--   This is the induction step in the descent of a quasi-compact, quasi-separated, finitely presented scheme over $A$ to a finitely generated subalgebra of $A$ (EGA IV, 8.8.2 and 8.10.5): two quasi-compact opens covering $X$ that each admit models at arbitrarily large finite stages are glued over a common stage. It is used by [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation), which runs the induction over a finite cover of $X$ by affines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation
    {A₀ R A : Type u} [CommRing A₀] [CommRing R] [CommRing A] [Algebra A₀ R] [Algebra R A] [Algebra A₀ A]
    [IsScalarTower A₀ R A] [Algebra.FiniteType A₀ R]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFinitePresentation g]
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (hUc : IsCompact (U : Set ↥X)) (hVc : IsCompact (V : Set ↥X))
    (hU : ∀ SS : Finset A, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : (U : Scheme.{u}) ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π (U.ι ≫ g) f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
    (hV : ∀ SS : Finset A, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : (V : Scheme.{u}) ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π (V.ι ≫ g) f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))))
    (SS : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑SS : Set A) ⊆ T ∧ Set.range (algebraMap R A) ⊆ T ∧
        ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
          LocallyOfFinitePresentation f₀ ∧ QuasiCompact f₀ ∧ QuasiSeparated f₀ ∧
          IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A))) := by sorry
