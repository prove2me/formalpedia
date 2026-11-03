-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:23:14.53869+00:00
-- url     : https://prove2.me/theorems/e53a9ae1-c520-4676-9434-f74b100dee57
-- title:
--   Original BV finite-horizon full Stieltjes cash and strict-survival terminal are jointly integrable
-- statement:
--   At every nonnegative deterministic horizon, the original bounded-variation Levy path, original admissible dividend strategy, complete payment-time Stieltjes mass including rightpayment atoms, and the strictly surviving postrightpayment terminal are both integrable. No stopped martingale or surrogate payout assumptions.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), stopped bound (5.13), exact two observable L1 terms of W7-04 target 0618723a-bb0b-4fa0-94bc-4def7af7aafa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_strict_survival_terminal_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P ∧
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0) P := by sorry
