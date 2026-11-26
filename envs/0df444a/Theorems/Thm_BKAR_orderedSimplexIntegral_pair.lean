-- Prove2me | Theorems.Thm_BKAR_orderedSimplexIntegral_pair
-- name    : BKAR.orderedSimplexIntegral_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:36:59.700796+00:00
-- url     : https://prove2.me/theorems/f6a6bce8-f4ac-5fdd-8cac-d553c10c2ed2
-- title:
--   BKAR: ordered Simplex Integral pair
-- statement:
--   The BKAR construction uses the ordered Simplex Integral pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L77-L80
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedSimplex.lean#L77-L80

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.orderedSimplexIntegral_pair (e₁ e₂ : Edge V) (f : List ℝ → ℝ) :
    orderedSimplexIntegral [e₁, e₂] f =
      ∫ t₁ in 0..(1 : ℝ), ∫ t₂ in 0..t₁, f [t₁, t₂] := by sorry
