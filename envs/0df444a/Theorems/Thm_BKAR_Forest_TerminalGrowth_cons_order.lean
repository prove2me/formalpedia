-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_order
-- name    : BKAR.Forest.TerminalGrowth.cons_order
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:05.825803+00:00
-- url     : https://prove2.me/theorems/952eae09-ef86-5d9d-8f74-9416ba712203
-- title:
--   Terminal Growth: cons order
-- statement:
--   The Terminal Growth construction uses the cons order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L82-L85
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L82-L85

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.cons_order {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).order = e :: tail.order := by sorry
