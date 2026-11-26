-- Prove2me | Theorems.Thm_BKAR_OrderedSimplexParams_le_head_of_mem_tail
-- name    : BKAR.OrderedSimplexParams.le_head_of_mem_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:07.041685+00:00
-- url     : https://prove2.me/theorems/e3f358cb-27aa-519e-934c-c56faccca7c9
-- title:
--   Ordered Simplex Params: le head of mem tail
-- statement:
--   The Ordered Simplex Params construction uses the le head of mem tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L138-L141
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L138-L141

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.OrderedSimplexParams

theorem BKAR.OrderedSimplexParams.le_head_of_mem_tail {top t s : ℝ} {ts : List ℝ}
    (h : OrderedSimplexParams top (t :: ts)) (hs : s ∈ ts) :
    s ≤ t := by sorry
