-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:32:37.186253+00:00
-- url     : https://prove2.me/theorems/202efe84-7645-4b70-b72a-cf5102785b25
-- title:
--   Unconditional ENNReal reciprocal cutoff monotone convergence to complete jump total
-- statement:
--   For any nonnegative extended-real indexed jump magnitudes, the supremum over natural reciprocal size-cutoffs of truncated tsums equals the full tsum, with no countability, integrability or separate coverage assumption. This uses the reciprocal ENNReal thresholds tending to zero and the generic finite-subset monotone-convergence core.
-- source:
--   Pinned Mathlib ENNReal.tendsto_inv_nat_nhds_zero, ENNReal.inv_le_inv and accepted avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_cutoff_tsum_monotone_convergence_core

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Reciprocal natural-number cutoffs exhaust an arbitrary ENNReal tsum,
including unbounded and uncountable index sets. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_reciprocal_cutoff_tsum_eq_full
    {α : Type*} (f : α → ℝ≥0∞) :
    (⨆ n : ℕ, ∑' a : α,
      if (n : ℝ≥0∞)⁻¹ < f a then f a else 0) =
      ∑' a : α, f a := by sorry
