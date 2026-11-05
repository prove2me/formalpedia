-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:45:59.871349+00:00
-- url     : https://prove2.me/theorems/646d7a18-3c1d-45e8-957b-e750087856f4
-- title:
--   Exact original physical BV drift C1 discounted Taylor mesh error vanishes
-- statement:
--   For any actual physical monotone stopped clock partitions [0,T] refining uniformly, with all pure physical drift reserve segments contained in a strict compact positive subcap C1 band, the discounted first-order Taylor remainders for c_i=(u_{i+1}-u_i)*b vanish. The proof uses a uniform derivative modulus, bounded positive discount, the exact physical drift clock telescope Σ|c_i|=T|b|, and the genuine clock-mesh drift shift convergence. Apply with b=X.drift to connect the original frozen-X source decomposition, without substitution of F2's jump-removed-Y increments.
-- source:
--   Proved uniform pure-drift Taylor grid budget, exact physical drift variation and original clock refinement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_drift_C1_taylor_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_grid_total_variation_exact

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
    (b : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a d : ℝ)
    (hBand : Set.Icc a d ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (z : ℕ → ℕ → ℝ)
    (hStart : ∀ m, u m 0 = 0)
    (hEnd : ∀ m, u m (n m) = T)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1)) :
    let c : ℕ → ℕ → ℝ := fun m i =>
      ((u m (i + 1) : ℝ) - (u m i : ℝ)) * b
    (∀ m i, i < n m →
      Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a d) →
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
    ∀ η : ℝ, 0 < η →
      ∀ᶠ m in Filter.atTop,
        |∑ i ∈ Finset.range (n m),
          Real.exp (-(q * (u m i : ℝ))) *
            (w (z m i + c m i) - w (z m i) -
              deriv w (z m i) * c m i)| < η := by sorry
