-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_support_eq_initial_support_of_order_eq_nil
-- name    : BKAR.Forest.TerminalGrowth.support_eq_initial_support_of_order_eq_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:11.962893+00:00
-- url     : https://prove2.me/theorems/2744f783-2d82-47f0-9031-9f6cb62c392d
-- title:
--   Terminal Growth: support eq initial support of order eq nil
-- statement:
--   If a terminal branch carries no growth order, its support is the support of
--   the initial forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L135-L139
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L135-L139

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.support_eq_initial_support_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = []) :
    data.support = F.support := by sorry
