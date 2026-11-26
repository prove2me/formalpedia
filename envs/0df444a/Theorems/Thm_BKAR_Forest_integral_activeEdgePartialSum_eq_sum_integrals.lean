-- Prove2me | Theorems.Thm_BKAR_Forest_integral_activeEdgePartialSum_eq_sum_integrals
-- name    : BKAR.Forest.integral_activeEdgePartialSum_eq_sum_integrals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:28.615842+00:00
-- url     : https://prove2.me/theorems/e0f8e42e-780c-4038-8f49-1c02575005de
-- title:
--   Forest: integral active Edge Partial Sum eq sum integrals
-- statement:
--   Split the integral of the differential right-hand side into the finite
--   sum of one-edge integrals over the active edges of the forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L344-L359
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L344-L359

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_activeEdgePartialSum_eq_sum_integrals (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      Finset.sum F.activeEdges
        (fun e => ∫ t in a..b,
          partialDeriv e ρ (F.interpWithFill u t)) := by sorry
