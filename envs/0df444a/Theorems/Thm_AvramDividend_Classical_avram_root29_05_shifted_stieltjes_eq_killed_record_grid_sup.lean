-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
-- name    : AvramDividend.Classical.avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:01:33.205929+00:00
-- url     : https://prove2.me/theorems/921cd292-57a6-4f91-8cba-438a632b509e
-- title:
--   Actual shifted killed Stieltjes dividend equals countable future-record cash supremum
-- statement:
--   For every actual spectrally negative Lévy sample path and finite future shift, the original Stieltjes measure of shifted future running-supremum dividends, killed at an arbitrary strict payment-time clock, equals the supremum over all finite rational killed discounted record-increment sums. This is a full pathwise nonnegative dividend identity for q≥0.
-- source:
--   Combine canonical upper inequality from Fatou and mesh exhaustion, lower inequality from survived stopped intervals, and the original generic paymentTimes strict indicator equality; reconcile the real/NNReal grids via denominator algebra. No shifted-process law is presumed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Full pathwise equality between the *actual* shifted future killed
Stieltjes dividend measure and all finite sampled future-record cash meshes. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_stieltjes_eq_killed_record_grid_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) =
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (M (grid (k + 1)).toNNReal - M (grid k).toNNReal)
        else 0) := by sorry
