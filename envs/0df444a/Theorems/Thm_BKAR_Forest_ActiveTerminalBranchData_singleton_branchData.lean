-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_branchData
-- name    : BKAR.Forest.ActiveTerminalBranchData.singleton_branchData
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:59.71916+00:00
-- url     : https://prove2.me/theorems/89159499-c6b3-4f89-9cd2-be712f53dd14
-- title:
--   Active Terminal Branch Data: singleton branch Data
-- statement:
--   The Active Terminal Branch Data construction uses the singleton branch Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L371-L378
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L371-L378

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.singleton_branchData
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions hterm).branchData =
      ActiveBranchData.singleton extensions := by sorry
