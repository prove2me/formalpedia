-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
-- name    : BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:43:53.462567+00:00
-- url     : https://prove2.me/theorems/2bf2a83f-a8d9-4979-9642-ddb2bca6f48a
-- title:
--   Active Terminal Branch Data: singleton branch Integral Aux eq sum integrals mixed Partial List standard Interp
-- statement:
--   Terminal singleton active-terminal branches in the standard
--   terminal-interpolation form.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L553-L568
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L553-L568

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegralAux top u
        (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) := by sorry
