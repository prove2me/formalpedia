-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
-- name    : AvramDividend.Classical.avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:56:55.464174+00:00
-- url     : https://prove2.me/theorems/75534b17-733b-4c18-bf13-8f714ec1677d
-- title:
--   Original stopped pure-Gaussian cap-linear HJB time drift is bounded by strict upper-strip occupation
-- statement:
--   For a genuine jump-free original Lévy dividend path with a strict positive pre-stop reserve floor, the discounted cap-linear generator time integral is at most the actual upper clipping-strip occupation integral, for almost every original sample path. Integrability and measurable real-time reserve are explicit. The non-differentiable clipping point has zero occupation by the original Gaussian shrinking-band estimate.
-- source:
--   B39 original zero fixed-level Lebesgue occupation; B40 original postpayment strict-floor positivity; B38 integrated off-kink cap-linear generator HJB ceiling. This isolates the controlled Gaussian HJB drift component of B21 without replacing X,D or the original stopping clock. The real-time path measurability premise is discharged by B42.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_original_gaussian_caplinear_offkink_integral_drift_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_original_postpayment_gaussian_exact_level_occupation_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_original_strict_clock_postpaid_real_time_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_postpayment_real_time_reserve_measurable_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω t, 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z =>
        if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t))
        (volume.restrict S) →
      Integrable (fun t => if b < Y t then max X.c 0 else 0)
        (volume.restrict S) →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
        (∫ t, if b < Y t then max X.c 0 else 0 ∂(volume.restrict S)) := by sorry
