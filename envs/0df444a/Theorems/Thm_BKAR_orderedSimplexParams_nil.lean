-- Prove2me | Theorems.Thm_BKAR_orderedSimplexParams_nil
-- name    : BKAR.orderedSimplexParams_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:16.013945+00:00
-- url     : https://prove2.me/theorems/186a08a0-4c42-415c-bac7-912e438a06b3
-- title:
--   BKAR: ordered Simplex Params nil
-- statement:
--   The BKAR construction uses the ordered Simplex Params nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L83-L85
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L83-L85

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexParams_nil (top : ℝ) :
    OrderedSimplexParams top [] := by sorry
