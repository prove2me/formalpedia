-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
-- name    : BKAR.Forest.TerminalGrowth.support_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:53.171473+00:00
-- url     : https://prove2.me/theorems/a81ab5fc-03e3-5f8c-ace3-648046c0f891
-- title:
--   Terminal Growth: support edges
-- statement:
--   The Terminal Growth construction uses the support edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L109-L111
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L109-L111

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_support_edges

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.support_edges (data : TerminalGrowth F) :
    data.support.edges = data.terminal.edges := by sorry
