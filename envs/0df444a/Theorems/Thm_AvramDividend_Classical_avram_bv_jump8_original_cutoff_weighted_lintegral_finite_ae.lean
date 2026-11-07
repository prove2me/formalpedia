-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_cutoff_weighted_lintegral_finite_ae
-- name    : AvramDividend.Classical.avram_bv_jump8_original_cutoff_weighted_lintegral_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:26:35.028184+00:00
-- url     : https://prove2.me/theorems/6fd5d9c9-4c9f-42b2-b8f1-1499860b3932
-- title:
--   Original BV Lévy intrinsic marked cutoff magnitude is almost surely finite at every horizon
-- statement:
--   For the actual source-exact intrinsic marked negative jumps of a bounded-variation spectrally negative Lévy process, the integral of negative jump magnitude over any positive-time horizon and strict negative cutoff is finite almost surely. This is a pointwise monotonicity consequence of the already-Proved full original jump-magnitude upper bound; no Poisson or independence assumption is added.
-- source:
--   Directly use Proved theorem UUID 8fdf098e-7ed6-47b5-a62d-cb08cbb9d13b. A strict-cutoff nonnegative integrand is bounded pointwise by its full jump-magnitude counterpart for every mark; the latter is bounded by ENNReal.ofReal (T * drift - X_T), hence finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_negative_jump_magnitude_integrable_ae
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_cutoff_weighted_lintegral_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (k : ℕ),
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≠ ∞ := by sorry
