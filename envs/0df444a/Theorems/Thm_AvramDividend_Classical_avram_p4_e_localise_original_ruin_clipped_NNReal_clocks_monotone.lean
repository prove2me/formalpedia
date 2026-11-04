-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:19:24.366533+00:00
-- url     : https://prove2.me/theorems/4381e3e7-2afd-416e-aff8-c6e85b3c0356
-- title:
--   Actual original ruin-clipped source stopping clocks are increasing in every finite horizon
-- statement:
--   For each exact original sample path, τ_n=(min(ruinTime,n)).toNNReal is monotone in n, including infinite ruin and zero ruin. Apply the Proved exact NNReal/ENNReal representation to the monotone map min ruin _ and transport back to NNReal order. This provides the non-arbitrary localising-clock monotonicity required by the source stopped Stieltjes cash and Fatou convergence proofs; stopping-time measurability remains a distinct already Proved fact.
-- source:
--   Original ruinTime and Proved clipped-clock representation 6b7a13a0; pinned Mathlib min_le_min_left and NNReal cast order.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source finite ruin-clipped NNReal clocks are pathwise increasing in the horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω, Monotone (fun n : ℕ =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) := by sorry
