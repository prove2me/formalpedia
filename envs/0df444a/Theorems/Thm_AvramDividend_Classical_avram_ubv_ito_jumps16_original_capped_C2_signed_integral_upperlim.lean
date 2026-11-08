-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:42:52.699593+00:00
-- url     : https://prove2.me/theorems/54254545-6e31-40ef-b775-420460089b54
-- title:
--   Capped C2 actual infinite-activity Levy jump correction has signed one-sided integral upper limit
-- statement:
--   The true spectrally negative Levy process's jump correction has a one-sided signed measure-integral upper limit at a positive reserve, even when a mark reaches exactly zero. The source-exact law supplies the negative mark support; a uniform integrable quadratic energy envelope and the previously verified signed reverse-Fatou interface complete the limit transfer. No surrogate jump-diffusion process or finite activity is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_real_upperlim_ofReal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_signed_integral_upperlim

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps16_original_capped_C2_signed_integral_upperlim
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
    (habs : ∀ (n : ℕ) (z : ℝ),
      |w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)| ≤ h z)
    (hgabs : ∀ z : ℝ,
      |w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)| ≤ h z)
    (hfint : ∀ n : ℕ, Integrable (fun z : ℝ =>
      w (u n + z) - w (u n) -
        (if -1 < z then z * deriv w (u n) else 0)) X.ν)
    (hgint : Integrable (fun z : ℝ =>
      w (y + z) - w y -
        (if -1 < z then z * deriv w y else 0)) X.ν) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    Filter.limsup (fun n : ℕ => ∫ z, R (u n) z ∂X.ν) atTop ≤
      ∫ z, R y z ∂X.ν := by sorry
