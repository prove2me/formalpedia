-- Prove2me | Theorems.Thm_BKAR_Forest_integral_activeEdgePartialSum_eq_sub
-- name    : BKAR.Forest.integral_activeEdgePartialSum_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:18.777155+00:00
-- url     : https://prove2.me/theorems/d47bbac4-3c52-5f15-b265-f48b9ca933d7
-- title:
--   Forest: integral active Edge Partial Sum eq sub
-- statement:
--   Integrated form of the differential identity over one interpolation parameter.
--   This is the analytic one-step expansion behind the ordered forest recursion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L365-L376
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L365-L376

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_activeEdgePartialSum_eq_sub (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : IntervalIntegrable (fun t : ℝ => F.activeEdgePartialSum u ρ t)
      MeasureTheory.volume a b) :
    (∫ t in a..b, F.activeEdgePartialSum u ρ t) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) := by sorry
