-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegral_singleton
-- name    : BKAR.orderedSimplexIntegral_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:55.864883+00:00
-- url     : https://prove2.me/theorems/c88871e4-b5e4-5ed5-ab42-ad4e02341941
-- title:
--   BKAR: ordered Simplex Integral singleton
-- statement:
--   The BKAR construction uses the ordered Simplex Integral singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L73-L75
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L73-L75

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegral_singleton (e : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e] f = ∫ t in 0..(1 : ℝ), f [t] := by sorry
