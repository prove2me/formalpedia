-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_eq_sum_activeExtension_integrals_of_forall_tail_order_eq_nil
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_of_forall_tail_order_eq_nil
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:42:56.166914+00:00
-- url     : https://prove2.me/theorems/c3726b94-b9d5-57ca-8d36-5e6499f1b96a
-- title:
--   Active Terminal Branch Data: branch Integral Aux eq sum active Extension integrals of forall tail order eq nil
-- statement:
--   If every selected tail stops immediately, the local selected-terminal branch
--   sum is exactly the one-step active-extension remainder.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L198-L218
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L198-L218

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

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_eq_sum_activeExtension_integrals_of_forall_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (htail : ∀ e : {e // e ∈ F.activeEdges}, (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) := by sorry
