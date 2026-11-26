-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges_eq_toFinset_union
-- name    : BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:57.121341+00:00
-- url     : https://prove2.me/theorems/dc71f0f3-9cc3-5392-9e48-f5451b2f641f
-- title:
--   Terminal Growth: support edges eq to Finset union
-- statement:
--   The Terminal Growth construction uses the support edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L113-L115
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L113-L115

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges_eq_toFinset_union

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.support_edges_eq_toFinset_union (data : TerminalGrowth F) :
    data.support.edges = data.order.toFinset ∪ F.edges := by sorry
