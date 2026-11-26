-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_mem_Icc
-- name    : BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:56.456731+00:00
-- url     : https://prove2.me/theorems/902c98a3-823d-4d8f-854a-b685b86bd614
-- title:
--   Ordered Growth: branch Point mem Icc
-- statement:
--   The Ordered Growth construction uses the branch Point mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L113-L120
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L113-L120

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchPoint_mem_Icc (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts)
    (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 := by sorry
