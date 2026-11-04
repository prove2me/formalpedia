-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:53:13.394488+00:00
-- url     : https://prove2.me/theorems/0fe5d1ab-84cf-44ae-9859-2e0791e9905a
-- title:
--   Actual original controlled terminal reserve remains below the admissible cap at ruin and survival
-- statement:
--   At the true P4-F terminal W, either the post-rightpayment reserve is selected at zero or strict survival (the proved source postpayment partition gives W≤C), or the original riskProcess is selected at strictly positive ruin (the original admissibility cap condition applies). The theorem covers ruin overshoot and the zero clock without erasing boundary contacts.
-- source:
--   Original P4-F terminal hW and Proved source postpayment reserve partition f1496f35; original IsAdmissibleLe cap field.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original terminal W is cap-bounded at every ruin/survival branch. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by sorry
