-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_eq_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_eq_interpWithFill_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:29.505117+00:00
-- url     : https://prove2.me/theorems/e0ee562e-1023-5c5a-8168-0a68a7093bee
-- title:
--   Ordered Growth: branch Point eq interp With Fill of active Edges eq empty
-- statement:
--   The Ordered Growth construction uses the branch Point eq interp With Fill of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L129-L134
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L129-L134

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_eq_interpWithFill_of_activeEdges_eq_empty
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ts : List ℝ) (b : ℝ) (hG : G.activeEdges = ∅) :
    h.branchPoint u ts = G.interpWithFill (h.params u ts) b := by sorry
