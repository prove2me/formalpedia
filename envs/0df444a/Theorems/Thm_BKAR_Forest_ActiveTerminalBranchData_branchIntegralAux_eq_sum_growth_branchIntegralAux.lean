-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_growth_branchIntegralAux
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_growth_branchIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:25.314804+00:00
-- url     : https://prove2.me/theorems/dd3b9954-ff99-4bcc-a4b8-59909f9aac1f
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum growth branch Integral Aux
-- statement:
--   The active-terminal branch sum is the sum of the selected full terminal branch
--   integrals.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L495-L501
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L495-L501

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_growth_branchIntegralAux
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => (data.growth e).branchIntegralAux top u ρ) := by sorry
