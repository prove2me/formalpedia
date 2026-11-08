-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:20:50.245378+00:00
-- url     : https://prove2.me/theorems/fe04bad8-cfbb-42f5-b9bf-29aa8433b052
-- title:
--   Original Levy signed-jump shifted real integrals inherit one-sided infinite-activity upper limit
-- statement:
--   For the genuine spectrally negative Levy process and its possibly infinite-activity jump measure, the accepted upper limit for uniformly dominated shifted nonnegative extended integrals transports to real Bochner integrals. The original finite quadratic energy supplies the common bound and prevents any infinity-to-real loss; the argument keeps the actual original measure and permits arbitrary negative-mark atoms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (habs : ∀ n z, |f n z| ≤ h z)
    (hgabs : ∀ z, |g z| ≤ h z)
    (hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ≤
        ENNReal.ofReal (h z + g z)) :
    Filter.limsup
      (fun n : ℕ => ∫ z, h z + f n z ∂X.ν) atTop ≤
      ∫ z, h z + g z ∂X.ν := by sorry
