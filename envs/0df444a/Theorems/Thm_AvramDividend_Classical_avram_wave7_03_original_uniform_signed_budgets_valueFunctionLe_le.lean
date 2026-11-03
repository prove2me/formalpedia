-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
-- name    : AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:01:51.218525+00:00
-- url     : https://prove2.me/theorems/82c6abb7-6ed9-4412-846e-c91216cb73d7
-- title:
--   Canonical capped dividend value supremum bounded by uniform genuine signed Stieltjes budgets
-- statement:
--   If every cap-admissible original dividend strategy has expected real discounted Stieltjes cash bounded by the same finite real B on every positive integer time horizon, then the canonical original valueFunctionLe X q C x, the supremum over all capped admissible strategies of complete ruin-stopped ENNReal dividendValue, is ≤ ENNReal.ofReal B. This is a formal exact source and measure-theoretic bridge into the original optimisation object, not a claim to establish the stochastic HJB budget premise for all strategies.
-- source:
--   Proved original uniform signed horizon Stieltjes budget to perpetual ENNReal bound 1caf0f13, canonical definition valueFunctionLe, two applications of iSup_le.

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

theorem AvramDividend.Classical.avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hBudget : ∀ (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
      (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunctionLe X q C x ≤ ENNReal.ofReal B := by sorry
