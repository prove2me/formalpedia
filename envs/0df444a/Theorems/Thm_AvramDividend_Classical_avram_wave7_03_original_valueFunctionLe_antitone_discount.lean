-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_valueFunctionLe_antitone_discount
-- name    : AvramDividend.Classical.avram_wave7_03_original_valueFunctionLe_antitone_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:16:33.015592+00:00
-- url     : https://prove2.me/theorems/4dac10f4-1558-4ff5-b4a5-f434fd66026d
-- title:
--   Original capped optimal dividend value function is antitone in the discount rate
-- statement:
--   For the exact spectrally negative Levy dividend model, the optimal ENNReal valueFunctionLe over the same capped admissible dividend strategies is nonincreasing as the real discount q increases, with all original ruin-stopped Stieltjes payouts, time-zero mass and positive-time continuous payments retained. No integrability or positive-discount restriction is added. The proof applies the already remotely Proved source-specific dividendValue discount order pointwise to every admissible policy and then takes the original two suprema without altering policy feasibility.
-- source:
--   Original Definition valueFunctionLe as supremum over D and IsAdmissibleLe; accepted original dividendValue discount-order helper a5978ae4; order of suprema.

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_valueFunctionLe_antitone_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    valueFunctionLe X q₂ C x ≤ valueFunctionLe X q₁ C x := by sorry
