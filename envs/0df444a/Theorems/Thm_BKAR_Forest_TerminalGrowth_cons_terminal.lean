-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_terminal
-- name    : BKAR.Forest.TerminalGrowth.cons_terminal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:26.768497+00:00
-- url     : https://prove2.me/theorems/943d6e89-04fc-4ed0-9131-e7407f166dbc
-- title:
--   Terminal Growth: cons terminal
-- statement:
--   The Terminal Growth construction uses the cons terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L87-L90
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L87-L90

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

theorem BKAR.Forest.TerminalGrowth.cons_terminal {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).terminal = tail.terminal := by sorry
