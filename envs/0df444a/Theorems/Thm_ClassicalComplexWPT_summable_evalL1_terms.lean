-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_evalL1_terms
-- name    : ClassicalComplexWPT.summable_evalL1_terms
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:58:00.468461+00:00
-- url     : https://prove2.me/theorems/dd292614-7a84-514f-840b-4515da472a51
-- title:
--   Classical Complex WPT: summable eval L1 terms
-- statement:
--   The Classical Complex WPT construction uses the summable eval L1 terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L306-L309
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L306-L309

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Finsupp.Weight
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
variable {S : Type*}

theorem ClassicalComplexWPT.summable_evalL1_terms (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) :
    Summable (fun a ↦ f a * monomial y a) := by sorry
