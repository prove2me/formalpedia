-- Prove2me | Theorems.Thm_BKAR_Forest_intervalIntegrable_activeEdgePartialSum
-- name    : BKAR.Forest.intervalIntegrable_activeEdgePartialSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:04.397245+00:00
-- url     : https://prove2.me/theorems/d79de091-0fee-48cc-8824-afb13aea1f8c
-- title:
--   Forest: interval Integrable active Edge Partial Sum
-- statement:
--   The differential right-hand side is interval integrable once each active-edge
--   partial derivative is interval integrable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L323-L338
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L323-L338

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.intervalIntegrable_activeEdgePartialSum (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b := by sorry
