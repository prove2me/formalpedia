-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_finite_cap_candidate_terminal_range_bounded
-- name    : AvramDividend.Classical.avram_wave6_08_original_finite_cap_candidate_terminal_range_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:14:18.532436+00:00
-- url     : https://prove2.me/theorems/d6901dc1-5d14-4bf9-a80d-445f24326359
-- title:
--   Original admissible finite-cap reserve has uniformly bounded continuous verification-value range through time zero
-- statement:
--   For the original spectrally negative Lévy process and an actual IsAdmissibleLe dividend strategy with positive finite cap, all pre-ruin reserves, including zero-time and equality with the cap, lie in the compact interval [0,c]. Any continuous verification candidate on the nonnegative half-line consequently has bounded real values on the entire original pre-ruin path family, uniformly over the original probability-space sample and time. This is the terminal-value localisation bound, not a conditional stochastic estimate.
-- source:
--   Proved original initial capital nonnegative, exact capped riskProcess range including zero, and finite-cap real reserve upper bound; compact continuous image.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_admissible_finite_cap_reserve_le_including_zero

open MeasureTheory Set Bornology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_finite_cap_candidate_terminal_range_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) :
    Bornology.IsBounded { z : ℝ | ∃ ω : Ω, ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < ruinTime X x D ω ∧
      z = w (riskProcess X x D t ω) } := by sorry
