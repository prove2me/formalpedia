-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_growth
-- name    : BKAR.Forest.TerminalGrowth.cons_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:23.770374+00:00
-- url     : https://prove2.me/theorems/8409f302-9889-54cf-86e8-d465f9e529b3
-- title:
--   Terminal Growth: cons growth
-- statement:
--   The Terminal Growth construction uses the cons growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L92-L95
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L92-L95

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

theorem BKAR.Forest.TerminalGrowth.cons_growth {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).growth = h.consGrowth tail.growth := by sorry
