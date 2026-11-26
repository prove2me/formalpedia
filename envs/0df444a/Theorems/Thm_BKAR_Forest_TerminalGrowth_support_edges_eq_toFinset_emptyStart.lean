-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_emptyStart
-- name    : BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:54.956746+00:00
-- url     : https://prove2.me/theorems/d02ef187-0d08-5595-89b2-882a3519606d
-- title:
--   Terminal Growth: support edges eq to Finset empty Start
-- statement:
--   The Terminal Growth construction uses the support edges eq to Finset empty Start property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L178-L182
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L178-L182

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.support.edges = data.order.toFinset := by sorry
