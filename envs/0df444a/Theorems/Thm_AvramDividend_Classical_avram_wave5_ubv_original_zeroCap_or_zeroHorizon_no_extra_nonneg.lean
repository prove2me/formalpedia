-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_zeroCap_or_zeroHorizon_no_extra_nonneg
-- name    : AvramDividend.Classical.avram_wave5_ubv_original_zeroCap_or_zeroHorizon_no_extra_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:47:11.740816+00:00
-- url     : https://prove2.me/theorems/3f3e6ab3-ac98-4ee1-ac3e-813437cf0d51
-- title:
--   Original-source zero-cap or zero-horizon UBV verification without a separate nonnegativity premise
-- statement:
--   For the same original SpectrallyNegativeLevy P 𝓕 and IsAdmissibleLe strategy D as the corrected UBV core, obtain the exact full discounted expected dividend inequality whenever C=0 or T=0. Retain the corrected core's assumptions and hJump, but do not demand the redundant auxiliary hw_nonneg assumption: its proof follows from 0≤w(0) and the gradient/secant on [0,C], and is imported from an already Proved same-source theorem. This is a zero-boundary consumer bridge reusing the Proved corrected zero-cap/zero-horizon result, not a new Stieltjes or Itô–Meyer proof; no positive-cap, w(0)=0, no-creeping or boundary C2 assumptions are introduced.
-- source:
--   Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706; reuse Proved original preruin nonnegative a81e26e3-b329-4cf1-bd1f-7ce8d83fd66b and existing corrected zero-cap/zero-horizon theorem 1b8029fe-9712-44cb-9878-76ffba5fd6d3. No modifications of those targets or milestone.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_preruin_candidate_nonnegative_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_ubv_original_zeroCap_or_zeroHorizon_no_extra_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hBoundary : C = 0 ∨ T = 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
