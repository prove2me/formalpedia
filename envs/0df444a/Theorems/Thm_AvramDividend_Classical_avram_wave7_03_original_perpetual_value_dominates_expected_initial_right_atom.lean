-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_value_dominates_expected_initial_right_atom
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_value_dominates_expected_initial_right_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:57:42.56109+00:00
-- url     : https://prove2.me/theorems/8991f680-2e97-4e97-8eee-4b42b439b859
-- title:
--   Canonical original perpetual expected full Stieltjes dividend cash dominates expected time-zero right-limit atom
-- statement:
--   For the exact original Lévy process, dividend strategy and P, the canonical infinite-horizon dividendValue always dominates the original expected ENNReal right-limit time-zero dividend atom. This includes immediate-ruin paths: by source paymentTimes the time-zero payout remains payable even if ruinTime=0. The exact time-zero Stieltjes mass is provided by Proved original rightLimit measure equality and the Proved original zero-clock full discounted cash identity, and set-inclusion monotonicity lifts the bound to the perpetual payout. No finiteness, discount positivity or bounded-clock hypothesis is needed.
-- source:
--   Proved zero-clock original full Stieltjes reward 1fb597ac-8e48-41be-a4e3-03b7681f3915 and original Stieltjes mass d6ace15b-26cc-4400-be9b-8c4d19980128; Mathlib lintegral_mono_set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_value_dominates_expected_initial_right_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (rightLimit D 0 ω) ∂P) ≤
      dividendValue X q x D := by sorry
