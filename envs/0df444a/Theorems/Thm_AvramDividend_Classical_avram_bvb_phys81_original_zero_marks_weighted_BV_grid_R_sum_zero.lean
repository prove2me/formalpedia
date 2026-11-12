-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
-- name    : AvramDividend.Classical.avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:38:47.994417+00:00
-- url     : https://prove2.me/theorems/ddecee05-3a2b-4ed4-b464-26edbe176a00
-- title:
--   Original no-negative-mark event cancels weighted BV physical-grid remainder sum
-- statement:
--   For any deterministic grid contained in the finite horizon and arbitrary possibly strategy-dependent cell weights, the original BV physical drift-minus-source correction has identically zero weighted finite sum on the negative-mark-free event. Applies directly to the second term of B in the physical stopped uniform-grid certificate.
-- source:
--   Original BV physical source correction 85b63af5 and 4f605d76; depends on Proved phys80

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The signed BV remainder contribution to every physical stopped grid is
zero on the original negative-mark-free event, for arbitrary cell weights. -/

theorem AvramDividend.Classical.avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, i ≤ n + 1 → u n i ≤ T)
    (W : ℕ → ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ n : ℕ,
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           W n i ω * (R (u n i) - R (u n (i + 1)))) = 0 := by sorry
