-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
-- name    : AvramDividend.Classical.avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:06:15.213029+00:00
-- url     : https://prove2.me/theorems/ece7dc65-a943-4587-9de7-cae3261588d9
-- title:
--   Continuous Gaussian source minus locally finite-variation dividend correction has bounded reserve path on every compact horizon
-- statement:
--   For any continuous real source path and arbitrary locally bounded-variation correction on nonnegative time, their shifted difference is bounded between finite real constants throughout every compact time horizon. This is the deterministic compact-range input needed for any correct occupation-density support theorem for the original Gaussian reserve, and preserves the actual source and dividend correction.
-- source:
--   Hard Gaussian B243 semimartingale local-time existence: deterministic compact-range premise on finite horizons via B244 and compact continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB245_continuous_source_minus_locally_BV_reserve_compact_bound
    (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (d : ℝ≥0 → ℝ)
    (hd : LocallyBoundedVariationOn d Set.univ)
    (x : ℝ) (T : ℝ≥0) :
    ∃ lo hi : ℝ, ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
      lo ≤ x + f t - d t ∧ x + f t - d t ≤ hi := by sorry
