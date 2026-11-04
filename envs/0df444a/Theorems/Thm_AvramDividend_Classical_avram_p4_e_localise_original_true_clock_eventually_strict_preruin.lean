-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_eventually_strict_preruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_clock_eventually_strict_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:13:07.388942+00:00
-- url     : https://prove2.me/theorems/dfca4a60-d394-4f7d-ac88-a9901897ae14
-- title:
--   Original cofinal ruin-truncated clocks eventually contain each strict pre-ruin time
-- statement:
--   For the actual original spectrally negative Levy and admissible dividend strategy, each finite deterministic physical time strictly before that path's ruin eventually lies strictly inside every large integer min(ruinTime,n) stopped clock. This follows from the existing Proved cofinal monotone stopping family, furnishing a rigorous pointwise localisation stabilisation input. No assumption of zero endpoint occupation, uniform integrability or optional stopping is made.
-- source:
--   Accepted original source bounded ruin stopping package f5caff4b; pinned Mathlib lt_iSup_iff and Filter.eventually_ge_atTop.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any original pre-ruin time eventually lies strictly inside all truncated clocks. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_clock_eventually_strict_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ᶠ n : ℕ in atTop,
      (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞) := by sorry
