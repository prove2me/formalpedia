-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_perpetual_cash_finite
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_cash_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:47:47.060727+00:00
-- url     : https://prove2.me/theorems/c640ece7-c872-4825-96dd-b1051aac7b19
-- title:
--   Finite perpetual original ENNReal cash from uniformly budgeted signed real Stieltjes horizons
-- statement:
--   For the original Levy process, cap-admissible dividend strategy, original dividendMeasure, and full strict pre-ruin paymentTimes, a common finite real upper bound B on expected real discounted Stieltjes cash on every positive integer horizon implies the complete perpetual double ENNReal dividend integral is not top. This is a direct finiteness consequence of the accepted W7-03 uniform signed-to-ENNReal budget bridge, with no infinite-horizon signed real integral asserted.
-- source:
--   Accepted W7-03 original uniform signed horizon to perpetual ENNReal budget lemma 1caf0f13, and finiteness of ENNReal.ofReal B.

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

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_perpetual_cash_finite
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
        ∂(dividendMeasure D ω) ∂P) ≠ ⊤ := by sorry
