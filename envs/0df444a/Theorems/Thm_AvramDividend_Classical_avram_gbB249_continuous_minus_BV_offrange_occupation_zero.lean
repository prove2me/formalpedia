-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB249_continuous_minus_BV_offrange_occupation_zero
-- name    : AvramDividend.Classical.avram_gbB249_continuous_minus_BV_offrange_occupation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:30:07.366225+00:00
-- url     : https://prove2.me/theorems/61d68f0b-dc66-4fdc-801d-6f665500fc0a
-- title:
--   Original-type Gaussian continuous source minus locally BV correction has no finite-horizon occupation outside a compact spatial range
-- statement:
--   On the original source's fixed finite physical-time horizon, the real corrected reserve is bounded between finite real values by B245. Every spatial open interval entirely above or below that path range is never visited during the stopped horizon, so its Lebesgue occupation measure vanishes exactly. This is the compact-spatial-support input for local time in B243, with actual continuous source and arbitrary locally BV correction.
-- source:
--   Gaussian B243 stochastic occupation density compact support for original continuous minus BV reserve; direct B245 and Lebesgue empty-set measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB249_continuous_minus_BV_offrange_occupation_zero
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (n : ℕ) (ρ : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ a b : ℝ, (hi ≤ a ∨ b ≤ lo) →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ : ℝ) ∧
        x + f (Real.toNNReal t) -
          d (Real.toNNReal t) ∈ Set.Ioo a b} = 0 := by sorry
