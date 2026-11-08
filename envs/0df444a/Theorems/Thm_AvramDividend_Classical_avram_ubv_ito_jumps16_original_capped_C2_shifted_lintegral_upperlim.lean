-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_capped_C2_shifted_lintegral_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps16_original_capped_C2_shifted_lintegral_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:17:14.095327+00:00
-- url     : https://prove2.me/theorems/1759faf2-e0fa-46f5-999e-e726d40f0abb
-- title:
--   Original infinite-activity Levy measure integrates capped C2 one-sided Taylor mark upper limits
-- statement:
--   The original spectrally negative Levy process inherits a nonnegative shifted-integral upper mesh limit for its original Taylor remainder, including arbitrary original negative-mark atoms at ruin contact. Assumes the original measure is concentrated on negative marks and a given measurable uniformly integrable Taylor energy envelope. The proof imports verified original pointwise mark and nonnegative integral upperlim results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_real_upperlim_ofReal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps16_original_capped_C2_shifted_lintegral_upperlim
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
    (hneg_ae : ∀ᵐ z ∂X.ν, z < 0)
    (hfmeas : ∀ n : ℕ, Measurable (fun z : ℝ =>
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)))
    (habs : ∀ (n : ℕ) (z : ℝ),
      |w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)| ≤ h z) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    Filter.limsup (fun n : ℕ =>
      ∫⁻ z, ENNReal.ofReal (h z + R (u n) z) ∂X.ν) atTop ≤
      ∫⁻ z, ENNReal.ofReal (h z + R y z) ∂X.ν := by sorry
