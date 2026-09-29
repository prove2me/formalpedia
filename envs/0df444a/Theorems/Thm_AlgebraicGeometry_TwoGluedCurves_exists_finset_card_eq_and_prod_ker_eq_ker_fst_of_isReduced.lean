-- Prove2me | Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
-- name    : AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/f9dc7fe3-4728-55ba-9136-5e06e2ccff9c
-- title:
--   Crossing subscheme in C₁ as product of n point ideals
-- statement:
--   Let $k$ be an algebraically closed field, let $X$ be a scheme with a morphism $x : X \to \operatorname{Spec} k$, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be schemes over $k$ with $c_1$ locally of finite type. Let $i_1$ be a morphism $C_1 \to X$ together with a proof that it followed by $x$ equals $c_1$, and likewise $i_2$ a morphism $C_2 \to X$ over $x$ with $c_2$; assume both underlying morphisms are closed immersions. Assume the scheme $P := C_1 \times_X C_2$ is reduced and that the cardinality of its underlying point set equals $n$, with $n > 0$ (so $P$ has exactly $n$ points). Then there is a finite set $N_1$ of $k$-points of $C_1$, i.e. of morphisms $p : \operatorname{Spec} k \to C_1$ with $p$ followed by $c_1$ the identity, such that: $N_1$ has exactly $n$ elements; the product of the kernel ideal sheaves $\ker p$ on $C_1$, over $p \in N_1$, equals the kernel ideal sheaf of the first projection $P \to C_1$; for each $p \in N_1$ the image in $X$ of $p$ followed by $i_1$ lies in the image of $P \to C_1 \to X$; and the image of $P \to C_1$ on underlying spaces is contained in the union of the images of the $p \in N_1$.
--
--   This identifies the scheme-theoretic intersection of two closed $k$-subschemes $C_1, C_2$ of $X$, when that intersection is reduced and finite, with a reduced divisor of $n$ rational points on $C_1$: the crossing ideal sheaf on $C_1$ factors as a product of ideal sheaves of $k$-points. It is used in the analysis of two glued curves, where twisting by the crossing ideal sheaf must be expressed in terms of point divisors for cohomological computations, and in the accompanying statement about the relative Picard functor of a two-glued-curve degeneration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TwoGluedCurves_exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

theorem AlgebraicGeometry.TwoGluedCurves.exists_finset_card_eq_and_prod_ker_eq_ker_fst_of_isReduced
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    {C₁ C₂ : Scheme.{u}} (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∃ N₁ : Finset {p : Spec (CommRingCat.of k) ⟶ C₁ // p ≫ c₁ = 𝟙 _},
      N₁.card = n ∧ (∏ p ∈ N₁, p.1.ker) = (pullback.fst i₁.1 i₂.1).ker ∧
      (∀ p ∈ N₁, Set.range (p.1 ≫ i₁.1).base ⊆ Set.range (pullback.fst i₁.1 i₂.1 ≫ i₁.1).base) ∧
      Set.range (pullback.fst i₁.1 i₂.1).base ⊆ ⋃ p ∈ N₁, Set.range p.1.base := by sorry
