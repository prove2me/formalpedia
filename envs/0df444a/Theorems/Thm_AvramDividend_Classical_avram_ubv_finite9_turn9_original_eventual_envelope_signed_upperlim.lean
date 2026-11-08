-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn9_original_eventual_envelope_signed_upperlim
-- name    : AvramDividend.Classical.avram_ubv_finite9_turn9_original_eventual_envelope_signed_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:48:54.44305+00:00
-- url     : https://prove2.me/theorems/deab2b1c-01c7-490f-b299-ff6b7fb36513
-- title:
--   Original signed jump-integral upper limit from an eventual quadratic envelope
-- statement:
--   For the original spectrally negative Lévy jump measure, a sequence of interior states converging to an interior point needs an integrable Taylor-remainder envelope only from some finite index onwards. Under the original compact smoothness and domination hypotheses for the limiting state, the signed jump-integral upper limit remains valid. Early out-of-band or nonintegrable approximants do not affect the limsup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite9_turn9_original_eventual_envelope_signed_upperlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y))
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (hint : Integrable h X.ν)
    (hfmeas : ∀ n : ℕ, Measurable (fun z : ℝ =>
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)))
    (hgmeas : Measurable (fun z : ℝ =>
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)))
    (hgabs : ∀ z : ℝ,
      |w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)| ≤ h z)
    (hgint : Integrable (fun z : ℝ =>
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)) X.ν)
    (hEventually : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ z : ℝ,
        |w (u n + z) - w (u n) -
          (if -1 < z then z * deriv w (u n) else 0)| ≤ h z) ∧
      Integrable (fun z : ℝ =>
        w (u n + z) - w (u n) -
          (if -1 < z then z * deriv w (u n) else 0)) X.ν) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    Filter.limsup (fun n : ℕ => ∫ z, R (u n) z ∂X.ν) atTop ≤
      ∫ z, R y z ∂X.ν := by sorry
