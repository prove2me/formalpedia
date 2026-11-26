-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_localFirstTailRemainder_def
-- name    : BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:54:55.241371+00:00
-- url     : https://prove2.me/theorems/b2ca730d-c8d1-59b5-8862-4680f65a48d4
-- title:
--   Active Terminal Branch Data: local First Tail Remainder def
-- statement:
--   The Active Terminal Branch Data construction uses the local First Tail Remainder def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L46-L60
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L46-L60

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

theorem BKAR.Forest.ActiveTerminalBranchData.localFirstTailRemainder_def
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ =
      (∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val (mixedPartialList es ρ))) -
        ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t) := by sorry
