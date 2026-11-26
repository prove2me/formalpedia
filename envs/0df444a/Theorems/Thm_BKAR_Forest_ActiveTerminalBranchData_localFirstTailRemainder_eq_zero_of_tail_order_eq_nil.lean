-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:47.514752+00:00
-- url     : https://prove2.me/theorems/ac1fd704-2bbf-42dd-bbe9-a60d361909a4
-- title:
--   Active Terminal Branch Data: local First Tail Remainder eq zero of tail order eq nil
-- statement:
--   A local first-tail error vanishes when the selected tail stops immediately.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L159-L192
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L159-L192

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ = 0 := by sorry
