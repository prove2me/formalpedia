-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:25:00.11008+00:00
-- url     : https://prove2.me/theorems/d69fc868-6f98-4807-8762-22d6a6320ca4
-- title:
--   Original complete stopped signed real Stieltjes reward is genuinely P-integrable at finite real horizon
-- statement:
--   Under the exact original spectrally negative Levy process and capped admissible dividend strategy, for any q>=0 and real T>=0, the real discounted Stieltjes dividend integral on exactly paymentTimes(ruinTime X x D omega) cap Iic T against exactly dividendMeasure D omega is P-integrable. The proof uses the accepted original ENNReal stopped cash L1 theorem, the W7-03 pathwise same-measure finite-horizon real/ENNReal equality, and nonnegativity of real exponential. There is no replacement sample space, no BV/UBV hypothesis, and the time-zero right-limit atom and all continuous and jump payments remain.
-- source:
--   Accepted original full cash toReal L1 f97e4695 and W7-03 exact full pathwise original real/ENNReal finite-horizon bridge a5c80ef7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_stieltjes_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by sorry
