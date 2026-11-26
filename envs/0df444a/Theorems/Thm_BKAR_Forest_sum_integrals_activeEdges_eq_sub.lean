-- Prove2me | Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_eq_sub
-- name    : BKAR.Forest.sum_integrals_activeEdges_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:51.856593+00:00
-- url     : https://prove2.me/theorems/2a9bc05f-37cd-5255-ab1b-0f72c748c2f1
-- title:
--   Forest: sum integrals active Edges eq sub
-- statement:
--   Integrated differential identity after expanding the differential right-hand side as
--   the active-edge sum.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L382-L396
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L382-L396

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_integrals_activeEdges_eq_sub (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        partialDeriv e ρ (F.interpWithFill u t)) =
      ρ (F.interpWithFill u b) - ρ (F.interpWithFill u a) := by sorry
