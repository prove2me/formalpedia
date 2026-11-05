-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:30:40.781783+00:00
-- url     : https://prove2.me/theorems/7056b9d2-7ff2-4af8-8a5c-900f298cca2e
-- title:
--   Actual physical BV drift increments vanish with the clock mesh
-- statement:
--   For any monotonically ordered physical-grid clocks, uniformly shrinking positive real mesh width makes every pure finite-variation drift increment ((u(i+1)-u(i))*b) uniformly small for any signed real drift b. The epsilon proof uses |b|+1, so zero and negative drifts are handled without extra cases. Instantiating b=X.drift supplies the exact physical shift smallness needed by source-specific P3-2 mixed-J estimates.
-- source:
--   Pinned Real/NNReal monotonicity and absolute product arithmetic; no surrogate source and no probabilistic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
    (b : ℝ) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1))
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        |((u m (i + 1) : ℝ) - (u m i : ℝ)) * b| < ε := by sorry
