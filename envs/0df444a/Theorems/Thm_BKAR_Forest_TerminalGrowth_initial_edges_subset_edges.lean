-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_initial_edges_subset_edges
-- name    : BKAR.Forest.TerminalGrowth.initial_edges_subset_edges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:59.418695+00:00
-- url     : https://prove2.me/theorems/b1c7bf7a-b828-5b08-9c9d-3392210f0da7
-- title:
--   Terminal Growth: initial edges subset edges
-- statement:
--   The Terminal Growth construction uses the initial edges subset edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L188-L190
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L188-L190

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_initial_edges_subset_edges

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.initial_edges_subset_edges (data : TerminalGrowth F) :
    F.edges ⊆ data.terminal.edges := by sorry
