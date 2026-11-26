-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_mem_Icc_one
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:15.308956+00:00
-- url     : https://prove2.me/theorems/242b7752-007f-5d4e-96b2-119bb8187fb7
-- title:
--   Ordered Growth: branch Point mem Icc one
-- statement:
--   The Ordered Growth construction uses the branch Point mem Icc one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L122-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L122-L127

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc_one (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 := by sorry
