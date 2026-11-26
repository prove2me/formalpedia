-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_terminal_edges_eq_toFinset_emptyStart
-- name    : BKAR.Forest.TerminalGrowth.terminal_edges_eq_toFinset_emptyStart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:46:45.294597+00:00
-- url     : https://prove2.me/theorems/d211b403-8788-4ed5-ad3d-3483e1a4093d
-- title:
--   Terminal Growth: terminal edges eq to Finset empty Start
-- statement:
--   The Terminal Growth construction uses the terminal edges eq to Finset empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L173-L176
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L173-L176

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.terminal_edges_eq_toFinset_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.terminal.edges = data.order.toFinset := by sorry
