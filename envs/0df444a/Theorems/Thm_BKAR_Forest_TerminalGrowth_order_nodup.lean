-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_order_nodup
-- name    : BKAR.Forest.TerminalGrowth.order_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:15.130133+00:00
-- url     : https://prove2.me/theorems/41da3227-07be-5772-9011-dbf14b6e10ec
-- title:
--   Terminal Growth: order nodup
-- statement:
--   The Terminal Growth construction uses the order nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L201-L203
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L201-L203

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_nodup

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.order_nodup (data : TerminalGrowth F) :
    data.order.Nodup := by sorry
