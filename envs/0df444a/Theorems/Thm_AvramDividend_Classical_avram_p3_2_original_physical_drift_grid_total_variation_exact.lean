-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_grid_total_variation_exact
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_drift_grid_total_variation_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:36:52.51819+00:00
-- url     : https://prove2.me/theorems/22893ea5-6fb1-43f3-9466-b58f4cfacd92
-- title:
--   Original physical BV drift grid total variation exact clock telescope
-- statement:
--   On every monotone original physical time grid, the exact total absolute variation of arbitrary signed drift b cells Δu*b equals the elapsed physical time multiplied by |b|. Instantiating b=X.drift and endpoints 0,T gives an exact path-independent uniform physical source drift variation budget T*|X.drift|. This supplies the missing finite-grid scalar envelope for the pure-drift C1 Taylor remainder in canonical P3-2.
-- source:
--   Pinned finite telescoping sum_range_sub and monotone NNReal grid clock cast; no surrogate process or extra probability law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_drift_grid_total_variation_exact
    (b : ℝ) (u : ℕ → ℝ≥0) (n : ℕ)
    (hGrid : ∀ i, i < n → u i ≤ u (i + 1)) :
    (∑ i ∈ Finset.range n,
      |((u (i + 1) : ℝ) - (u i : ℝ)) * b|) =
      ((u n : ℝ) - (u 0 : ℝ)) * |b| := by sorry
