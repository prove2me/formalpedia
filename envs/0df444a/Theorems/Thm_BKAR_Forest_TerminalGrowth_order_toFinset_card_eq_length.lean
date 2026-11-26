-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_toFinset_card_eq_length
-- name    : BKAR.Forest.TerminalGrowth.order_toFinset_card_eq_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:24.271405+00:00
-- url     : https://prove2.me/theorems/37f59238-c6a7-47f9-97c4-ffe187375a3e
-- title:
--   Terminal Growth: order to Finset card eq length
-- statement:
--   The Terminal Growth construction uses the order to Finset card eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L205-L207
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L205-L207

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_toFinset_card_eq_length

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_toFinset_card_eq_length (data : TerminalGrowth F) :
    data.order.toFinset.card = data.order.length := by sorry
