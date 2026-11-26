-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_def
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:53.931881+00:00
-- url     : https://prove2.me/theorems/95298e46-d36b-4a24-9549-40354bb0856d
-- title:
--   Ordered Growth: branch Point def
-- statement:
--   The Ordered Growth construction uses the branch Point def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L70-L73
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L70-L73

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_def (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    h.branchPoint u ts = G.standardInterp (h.params u ts) := by sorry
