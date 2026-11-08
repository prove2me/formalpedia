-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_signed_integral_upperlim
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps16_original_signed_integral_upperlim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:32:54.365302+00:00
-- url     : https://prove2.me/theorems/cb227aa7-0aa3-44ac-8971-b8f7c3ebb0e7
-- title:
--   Original infinite-activity Levy measure signed Taylor-integral reverse Fatou
-- statement:
--   The genuine spectrally negative Levy measure supports one-sided upper limits for signed Taylor correction integrals when a common integrable envelope dominates all corrections and their limit. The proof cancels this envelope from the previously proved shifted real-integral upper bound, using Bochner integral linearity and explicitly bounded signed integrals. No compound-Poisson substitution is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps16_original_signed_integral_upperlim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (hint : Integrable h X.ν)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (habs : ∀ n z, |f n z| ≤ h z)
    (hgabs : ∀ z, |g z| ≤ h z)
    (hfint : ∀ n, Integrable (f n) X.ν)
    (hgint : Integrable g X.ν)
    (hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ≤
        ENNReal.ofReal (h z + g z)) :
    Filter.limsup (fun n : ℕ => ∫ z, f n z ∂X.ν) atTop ≤
      ∫ z, g z ∂X.ν := by sorry
