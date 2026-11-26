-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegral_eq_sum_integrals_tail_partialDeriv
-- name    : BKAR.Forest.ActiveBranchData.branchIntegral_eq_sum_integrals_tail_partialDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:40.156848+00:00
-- url     : https://prove2.me/theorems/97ac6199-6ecd-54e4-b904-235a071b544c
-- title:
--   Active Branch Data: branch Integral eq sum integrals tail partial Deriv
-- statement:
--   Unit-simplex version of
--   `ActiveBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L158-L167
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L158-L167

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.branchIntegral_eq_sum_integrals_tail_partialDeriv
    (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) := by sorry
