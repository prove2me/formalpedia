-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_integrals_tail_partialDeriv
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:53:07.64725+00:00
-- url     : https://prove2.me/theorems/99ee35bf-0c1b-5def-8c71-457ac7c92851
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum integrals tail partial Deriv
-- statement:
--   Recursive form of the active-terminal branch sum after the first active edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L506-L516
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L506-L516

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_ActiveBranchData_branchIntegralAux_eq_sum_integrals_tail_partialDeriv
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) := by sorry
