-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_strict_survival_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_strict_survival_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:45:18.205136+00:00
-- url     : https://prove2.me/theorems/ab418409-bab1-4e73-8f3d-354a8f64e3a9
-- title:
--   Original BV strict-survival post-rightpayment terminal is integrable from actual admissible dividend path
-- statement:
--   The original bounded-variation Levy model and genuine original dividend strategy alone force the discounted post-rightpayment candidate terminal to be integrable on strict survival at each deterministic horizon, provided the test is continuous on nonnegative states and zero below zero. Original dividend monotonicity supplies the nonnegative initial right payment; original ruin and reserve lemmas supply measurability and survival solvency; the source drift ceiling bounds the surviving reserve.
-- source:
--   Avram-Palmowski-Pistorius Proposition 4(i), strictly surviving postpayment terminal in stopped inequality (5.13). Direct complete-integrability component required by W7-04 original source target 0618723a-bb0b-4fa0-94bc-4def7af7aafa; stronger application of source helper 73908043-0c0b-4925-b58d-0e147640ef86.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_strict_survival_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0) P := by sorry
