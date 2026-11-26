-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_of_initial_mem
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_of_initial_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:36.087019+00:00
-- url     : https://prove2.me/theorems/7a3975e2-151f-44c9-b8f7-75e705c71f45
-- title:
--   Ordered Growth: branch Point of initial mem
-- statement:
--   The Ordered Growth construction uses the branch Point of initial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L84-L87
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L84-L87

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_of_initial_mem (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.branchPoint u ts e = u ⟨e, he⟩ := by sorry
