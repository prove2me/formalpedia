-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_toFinset_subset_edges
-- name    : BKAR.Forest.TerminalGrowth.order_toFinset_subset_edges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:54.685371+00:00
-- url     : https://prove2.me/theorems/d0c113af-6195-5794-9926-f1493b6a7ec0
-- title:
--   Terminal Growth: order to Finset subset edges
-- statement:
--   The Terminal Growth construction uses the order to Finset subset edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L184-L186
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L184-L186

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_subset_edges

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_toFinset_subset_edges (data : TerminalGrowth F) :
    data.order.toFinset ⊆ data.terminal.edges := by sorry
