-- Prove2me | Theorems.Thm_Esgk_maximallyCircular_twoSamplePairSeparation
-- name    : Esgk.maximallyCircular_twoSamplePairSeparation
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-16T05:10:17.856073+00:00
-- url     : https://prove2.me/theorems/f01ebaf8-9511-4466-94e5-8fadaa228172
-- title:
--   Pair separation for two samples on a maximally circular curve
-- statement:
--   Let $G$ be an irreducible real plane polynomial of degree $d$, with real zero set $C$. Assume that $G$ is not a circle factor and is maximally circular: its local order at each of the two complex circular points at infinity is $d/2$.
--
--   For any two finite samples $S_1,S_2\subset C$, there are exceptional sets $\Delta_i\subset S_i\times S_i$, for $i=1,2$, satisfying
--
--   $$
--   |\Delta_i|\le 8d^2|S_i|.
--   $$
--
--   Within each sample, any two distinct retained pairs $(a,b),(a',b')\in(S_i\times S_i)\setminus\Delta_i$ have a finite common distance locus
--
--   $$
--   \bigl\{(x,y)\in C\times C:
--   \|x-a\|^2=\|y-b\|^2,\quad
--   \|x-a'\|^2=\|y-b'\|^2\bigr\}.
--   $$
--
--   The two conclusions hold simultaneously and separately within the two samples. The samples may be empty or overlap. No assertion is made about a pair from one sample compared with a pair from the other.

import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim

open Esgk
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

theorem Esgk.maximallyCircular_twoSamplePairSeparation
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S₁ S₂ : Finset PachDeZeeuw.Algebraic.Point2)
    (hS₁ : (S₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G)
    (hS₂ : (S₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ (Δ₁ : Finset (S₁ × S₁)) (Δ₂ : Finset (S₂ × S₂)),
      Δ₁.card ≤ 8 * G.totalDegree ^ 2 * S₁.card ∧
      Δ₂.card ≤ 8 * G.totalDegree ^ 2 * S₂.card ∧
      (∀ ij, ij ∉ Δ₁ → ∀ kl, kl ∉ Δ₁ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite) ∧
      (∀ ij, ij ∉ Δ₂ → ∀ kl, kl ∉ Δ₂ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite) := by sorry
