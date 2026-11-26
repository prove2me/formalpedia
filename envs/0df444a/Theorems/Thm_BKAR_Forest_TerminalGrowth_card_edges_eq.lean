-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_card_edges_eq
-- name    : BKAR.Forest.TerminalGrowth.card_edges_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:21.8046+00:00
-- url     : https://prove2.me/theorems/793c7b58-8937-5819-aaa9-be00f9e79e20
-- title:
--   Terminal Growth: card edges eq
-- statement:
--   The Terminal Growth construction uses the card edges eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L209-L211
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L209-L211

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_card_edges_eq

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.card_edges_eq (data : TerminalGrowth F) :
    data.terminal.edges.card = F.edges.card + data.order.length := by sorry
