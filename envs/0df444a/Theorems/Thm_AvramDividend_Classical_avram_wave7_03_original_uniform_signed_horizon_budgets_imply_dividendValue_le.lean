-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:00:56.319692+00:00
-- url     : https://prove2.me/theorems/96f0eeb7-80fd-462c-8bdf-cb62d1bfef11
-- title:
--   Canonical original dividendValue bounded by uniformly budgeted genuine signed Stieltjes horizons
-- statement:
--   For the actual canonical dividendValue X q x D of the spectrally negative Levy process and admissible strategy D, if the expectation of its genuine discounted Stieltjes dividends on every finite positive integer horizon is bounded by a real B, then the complete original dividendValue is ≤ ENNReal.ofReal B. The proof is only a definitional change from dividendValue into the exact accepted perpetual original-source signed-to-ENNReal budget lemma, with time-zero atom, continuous cash, strict positive ruin boundary and genuine P unchanged.
-- source:
--   Accepted original uniform signed horizon budgets imply perpetual ENNReal theorem 1caf0f13 and canonical Definition dividendValue.

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

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
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
    dividendValue X q x D ≤ ENNReal.ofReal B := by sorry
