-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_edges_eq_toFinset_union
-- name    : BKAR.Forest.TerminalGrowth.edges_eq_toFinset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:42:37.710061+00:00
-- url     : https://prove2.me/theorems/a23b374a-dc90-4628-9553-b25d6b4cc4c1
-- title:
--   Terminal Growth: edges eq to Finset union
-- statement:
--   The Terminal Growth construction uses the edges eq to Finset union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L101-L103
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L101-L103

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_edges_eq_toFinset_union

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.edges_eq_toFinset_union (data : TerminalGrowth F) :
    data.terminal.edges = data.order.toFinset ∪ F.edges := by sorry
