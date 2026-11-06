-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_signed_horizon_real_perpetual_bridge
-- name    : AvramDividend.Classical.avram_limit2_bv_signed_horizon_real_perpetual_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:20:21.244878+00:00
-- url     : https://prove2.me/theorems/1584045e-9c01-494b-b72b-20699420cf2b
-- title:
--   Original BV signed stopped horizons imply exact real perpetual discounted dividend cash bound
-- statement:
--   LIMIT-2 original BV signed-horizon real perpetual adapter
--
--   Original source assumptions are exactly those of the accepted BV bridge b1112496, with an explicit nonnegative B needed for the already-Proved real mean comparison. The signed positive-horizon cash and strict-survival post-right-payment terminal budget is kept unchanged, including Iic T, initial atoms, and original ruin time. Accepted b1112496 proves positive-horizon terminal integrability and bounded perpetual dividendValue. Its finite ENNReal value gives original full real Stieltjes payout L1 and the exact ofReal outer-mean identity by the Proved wave7_03 finite-value bridge. The already Proved avram_limit2 original mean comparison yields the real expected-payout bound. No terminal vanishing or equality-in-law.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_signed_horizon_real_perpetual_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ B) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0)) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
