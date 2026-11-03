-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:20:12.028353+00:00
-- url     : https://prove2.me/theorems/ead5faa1-7f66-43ce-a2c9-cb109aac1fde
-- title:
--   Original killed strict-survival HJB postrightpayment terminal jointly measurable in time and sample
-- statement:
--   The exact discounted nonnegative HJB continuation payoff, killed by the strict event t<ruinTime and evaluated after the original source dividend right-payment, is jointly measurable in physical time and sample. Hence any measurable random clock can be substituted without separate stopped-process adaptedness or changing the terminal convention.
-- source:
--   Source-specific BV/UBV stochastic verification support. Uses accepted original discounted exponential joint-time-path measurability 30c00aaa, genuine ruinTime measurability, original candidate continuity with negative-zero extension and exact rightLimit D. The log of the positive exponential recovers the actual reserve and measurability of its killed terminal, independent of stopping-time assumptions or the verification inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if (z.1 : ℝ≥0∞) < ruinTime X x D z.2 then
        max 0 (Real.exp (-(q * (z.1 : ℝ))) *
          w (x + X.X z.1 z.2 - rightLimit D z.1 z.2))
      else 0) := by sorry
