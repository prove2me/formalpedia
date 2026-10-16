-- Prove2me | Theorems.Thm_Esgk_maximallyCircular_pairSeparation
-- name    : Esgk.maximallyCircular_pairSeparation
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-16T05:09:20.489994+00:00
-- url     : https://prove2.me/theorems/712a873c-9027-4841-bd9f-0f90a1df9777
-- title:
--   Pair separation on a maximally circular curve
-- statement:
--   Let $G$ be an irreducible real plane polynomial of degree $d$, with real zero set $C$. Assume that $G$ is not a circle factor and is maximally circular: its local order at each of the two complex circular points at infinity is $d/2$.
--
--   For every finite sample $S\subset C$, there is an exceptional set of ordered pairs $\Delta\subset S\times S$ with
--
--   $$
--   |\Delta|\le 8d^2|S|
--   $$
--
--   such that any two distinct retained pairs $(a,b),(a',b')\in(S\times S)\setminus\Delta$ have a finite common distance locus
--
--   $$
--   \bigl\{(x,y)\in C\times C:
--   \|x-a\|^2=\|y-b\|^2,\quad
--   \|x-a'\|^2=\|y-b'\|^2\bigr\}.
--   $$
--
--   The sample may be empty. Absolute irreducibility over the complex numbers is not required.

import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageInfiniteCorrespondence
import Definitions.Def_Esgk_IrreduciblePlaneFunctionField
import Definitions.Def_Esgk_PlaneCircleFactor
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim

open Esgk
open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

theorem Esgk.maximallyCircular_pairSeparation
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ Δ : Finset (S × S),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card ∧
      ∀ ij, ij ∉ Δ → ∀ kl, kl ∉ Δ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by sorry
