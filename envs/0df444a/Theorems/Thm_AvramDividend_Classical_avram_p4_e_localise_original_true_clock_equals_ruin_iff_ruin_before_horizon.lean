-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_equals_ruin_iff_ruin_before_horizon
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_clock_equals_ruin_iff_ruin_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:30.688682+00:00
-- url     : https://prove2.me/theorems/d0d8e7f2-89a4-477a-957e-46be60a039a5
-- title:
--   Original clipped clock has reached ruin exactly when ruin time is at most the horizon
-- statement:
--   For actual X and D, the embedded original toNNReal clipped clock equals ruinTime exactly when ruinTime≤n. This distinguishes full-bookkeeping reserve at ruin from pre-ruin postpayment terminal W and handles infinite ruin consistently. It does not presume any dividend atom vanishes at the ruin horizon.
-- source:
--   Accepted original exact toNNReal clip equality 6b7a13a0 and min_eq_left_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original true stopped clock hits ruin precisely when ruin precedes the horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_clock_equals_ruin_iff_ruin_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) =
      ruinTime X x D ω ↔
    ruinTime X x D ω ≤ (n : ℝ≥0∞) := by sorry
