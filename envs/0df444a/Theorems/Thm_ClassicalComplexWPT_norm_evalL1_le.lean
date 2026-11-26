-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_evalL1_le
-- name    : ClassicalComplexWPT.norm_evalL1_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:11.67059+00:00
-- url     : https://prove2.me/theorems/4ca77b69-d011-5231-8b26-dc6bffb744f2
-- title:
--   Classical Complex WPT: norm eval L1 le
-- statement:
--   Evaluation on the unit polydisc is bounded by the coefficient `ℓ¹` norm.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L312-L323
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedSeries.lean#L312-L323

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

theorem ClassicalComplexWPT.norm_evalL1_le (f : L1Coeff (S →₀ ℕ)) (y : S → ℂ)
    (hy : ∀ i, ‖y i‖ ≤ 1) : ‖evalL1 f y‖ ≤ ‖f‖ := by sorry
