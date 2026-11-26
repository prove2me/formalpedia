-- Prove2me | Theorems.Thm_BKAR_orderedSimplexParams_cons
-- name    : BKAR.orderedSimplexParams_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:07.545395+00:00
-- url     : https://prove2.me/theorems/13916091-c931-5bb7-ac5f-38d2d4428cbc
-- title:
--   BKAR: ordered Simplex Params cons
-- statement:
--   The BKAR construction uses the ordered Simplex Params cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L88-L91
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L88-L91

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexParams_cons (top t : ℝ) (ts : List ℝ) :
    OrderedSimplexParams top (t :: ts) ↔
      0 ≤ t ∧ t ≤ top ∧ OrderedSimplexParams t ts := by sorry
