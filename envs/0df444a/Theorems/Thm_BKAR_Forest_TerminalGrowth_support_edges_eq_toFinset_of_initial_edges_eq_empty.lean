-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_of_initial_edges_eq_empty
-- name    : BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_of_initial_edges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:43:08.495979+00:00
-- url     : https://prove2.me/theorems/97def477-d074-5fff-868b-46dedfc6808f
-- title:
--   Terminal Growth: support edges eq to Finset of initial edges eq empty
-- statement:
--   The Terminal Growth construction uses the support edges eq to Finset of initial edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L168-L171
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L168-L171

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_of_initial_edges_eq_empty
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.support.edges = data.order.toFinset := by sorry
