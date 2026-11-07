-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_localised_reward_family_nonnegative
-- name    : AvramDividend.Classical.avram_p4_f14_original_localised_reward_family_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:48:13.969591+00:00
-- url     : https://prove2.me/theorems/7e8fc922-dcbf-490a-92dd-e2ebb31d31e5
-- title:
--   Every genuine UBV localised capped stopped dividend payoff is nonnegative
-- statement:
--   The original source discounted terminal-plus-closed-Stieltjes-dividend payoff is pointwise nonnegative for every physical localisation σ_k and sample path, by instantiating the already-proved original single-clock theorem. Supplies the positivity premise for Fatou/localisation downstream of the F14 stopped Itô witness.
-- source:
--   Genuine source family instantiation of public Proved theorem 5893451b-5c95-4460-b400-7bc3d2b67e65; retains exact right-payment boundary and cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f14_original_localised_reward_family_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ k ω, 0 ≤ F k ω := by sorry
