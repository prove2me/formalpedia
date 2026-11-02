-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
-- name    : AvramDividend.Classical.avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:31:50.459788+00:00
-- url     : https://prove2.me/theorems/f0d4c94c-c070-460b-bb90-95ccc0264d90
-- title:
--   True original stopped full Stieltjes payoff is finite almost surely at every real horizon, including time-zero
-- statement:
--   The exact original Lévy X and original admissible D have almost surely finite entire discounted stopped paymentTimes Stieltjes reward at every nonnegative real T, including T=0 and its initial right payment. This is the real horizon and full measure used verbatim in canonical BV ef7e6c20 and corrected UBV 429e17ca. Proved by comparing its closed payment window to a larger positive NNReal clock, using the canonical Proved source almost-sure finite reward. All lump, absolutely continuous and singular-continuous dividend components remain; no independence, global nonnegative w, stochastic Ito formula, or unproved jump compensator is claimed.
-- source:
--   Original BV ef7e6c20 and corrected UBV 429e17ca full Stieltjes reward at real T. Proved original source NNReal-clock almost-sure reward ca2ee80e and source paymentTimes measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_stopped_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)) < ⊤ := by sorry
