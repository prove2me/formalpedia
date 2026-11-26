-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_toFinset_disjoint_initial_edges
-- name    : BKAR.Forest.TerminalGrowth.order_toFinset_disjoint_initial_edges
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:21.105398+00:00
-- url     : https://prove2.me/theorems/f9435317-2a60-51a8-9e40-1cb41f8dfb07
-- title:
--   Terminal Growth: order to Finset disjoint initial edges
-- statement:
--   The Terminal Growth construction uses the order to Finset disjoint initial edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L197-L199
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L197-L199

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_disjoint_initial_edges

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_toFinset_disjoint_initial_edges (data : TerminalGrowth F) :
    Disjoint data.order.toFinset F.edges := by sorry
