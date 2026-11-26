-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_singleton_growth_growth_eq_singletonGrowth
-- name    : BKAR.Forest.ActiveTerminalBranchData.singleton_growth_growth_eq_singletonGrowth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:25:23.577804+00:00
-- url     : https://prove2.me/theorems/616599cf-3304-4791-adae-3de1cda9f607
-- title:
--   Active Terminal Branch Data: singleton growth growth eq singleton Growth
-- statement:
--   The Active Terminal Branch Data construction uses the singleton growth growth eq singleton Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L455-L463
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L455-L463

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.singleton_growth_growth_eq_singletonGrowth
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges}) :
    ((singleton extensions hterm).growth e).growth =
      (extensions e).singletonGrowth := by sorry
