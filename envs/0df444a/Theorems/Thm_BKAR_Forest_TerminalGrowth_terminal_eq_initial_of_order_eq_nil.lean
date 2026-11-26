-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_terminal_eq_initial_of_order_eq_nil
-- name    : BKAR.Forest.TerminalGrowth.terminal_eq_initial_of_order_eq_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:51.546745+00:00
-- url     : https://prove2.me/theorems/3c8b3c4a-7be8-40a3-b0d9-249360fec834
-- title:
--   Terminal Growth: terminal eq initial of order eq nil
-- statement:
--   If a terminal branch carries no growth order, its terminal forest is the
--   initial forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L121-L129
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L121-L129

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.terminal_eq_initial_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = []) :
    data.terminal = F := by sorry
