-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_monomial_le_one
-- name    : ClassicalComplexWPT.norm_monomial_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:30.891983+00:00
-- url     : https://prove2.me/theorems/5a453ab7-d924-5de2-86d3-813f9ff8649a
-- title:
--   Classical Complex WPT: norm monomial le one
-- statement:
--   The Classical Complex WPT construction uses the norm monomial le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L271-L281
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L271-L281

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

theorem ClassicalComplexWPT.norm_monomial_le_one (y : S → ℂ) (hy : ∀ i, ‖y i‖ ≤ 1) (a : S →₀ ℕ) :
    ‖monomial y a‖ ≤ 1 := by sorry
