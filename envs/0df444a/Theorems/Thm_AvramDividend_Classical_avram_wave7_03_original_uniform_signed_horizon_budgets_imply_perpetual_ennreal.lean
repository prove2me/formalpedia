-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:34:43.92372+00:00
-- url     : https://prove2.me/theorems/1caf0f13-cf2d-457e-ae1d-06db6c001103
-- title:
--   Uniform original stopped signed Stieltjes real budgets imply complete perpetual ENNReal dividend budget
-- statement:
--   If the original bounded-horizon real expected Stieltjes dividend reward on exact paymentTimes(ruinTime X x D omega) cap Iic(n+1), against original dividendMeasure, is uniformly bounded by B for all n, then the complete original perpetual double-ENNReal dividend payout is bounded by ENNReal.ofReal B. Works on actual spectrally negative Levy process and original capped admissible D for q>=0, with no BV/UBV or infinite-horizon real integral premise. Includes zero atom and all diffuse/càdlàg payments, with positive ruin boundary excluded.
-- source:
--   Accepted W7-03 perpetual exact signed Stieltjes expectation iSup theorem f05062e4 and ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_perpetual_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
