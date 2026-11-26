-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_mem_edges_of_mem_order
-- name    : BKAR.Forest.TerminalGrowth.mem_edges_of_mem_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:23:07.629768+00:00
-- url     : https://prove2.me/theorems/76fa6bde-7fa9-5c1f-8bfa-ebfea20bcfb2
-- title:
--   Terminal Growth: mem edges of mem order
-- statement:
--   The Terminal Growth construction uses the mem edges of mem order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L192-L195
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L192-L195

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.mem_edges_of_mem_order (data : TerminalGrowth F) {e : Edge V}
    (he : e ∈ data.order) :
    e ∈ data.terminal.edges := by sorry
