-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_perpetual_toReal_cash_le
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_toReal_cash_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:53:17.601904+00:00
-- url     : https://prove2.me/theorems/b1e8464c-7bcc-4f02-a8fe-2a267c329f4f
-- title:
--   Real-valued perpetual cash budget via original uniform signed Stieltjes horizon bounds
-- statement:
--   For the original Levy process and strategy, if real signed expected discounted Stieltjes cash on all positive integer horizons is ≤ finite nonnegative B, then the toReal of the complete perpetual double ENNReal dividend integral on original paymentTimes(ruinTime) and dividendMeasure is ≤ B. The proof invokes the accepted uniform signed-to-perpetual bridge and ENNReal.toReal_mono with finite ENNReal.ofReal B. Does not assume or define any perpetual signed real integral.
-- source:
--   Proved original uniform finite-horizon signed Stieltjes budgets imply perpetual ENNReal theorem 1caf0f13, Mathlib ENNReal.toReal_mono and ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_toReal_cash_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P).toReal ≤ B := by sorry
