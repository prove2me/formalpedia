-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_convolutionRight_le
-- name    : ClassicalComplexWPT.norm_convolutionRight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:51.36968+00:00
-- url     : https://prove2.me/theorems/ad8a44cf-01d4-4a64-8d95-eed9fcab3271
-- title:
--   Classical Complex WPT: norm convolution Right le
-- statement:
--   The Classical Complex WPT construction uses the norm convolution Right le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L125-L129
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L125-L129

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
variable {A : Type*} [AddCommMonoid A] [Finset.HasAntidiagonal A]

theorem ClassicalComplexWPT.norm_convolutionRight_le (g : L1Coeff A) : ‖convolutionRight g‖ ≤ ‖g‖ := by sorry
