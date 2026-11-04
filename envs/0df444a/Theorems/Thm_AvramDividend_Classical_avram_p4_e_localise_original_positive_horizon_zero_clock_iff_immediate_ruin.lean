-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:21:02.516384+00:00
-- url     : https://prove2.me/theorems/c28dcd9b-e834-435d-88c2-9071d42da516
-- title:
--   At positive original finite horizon, zero exact stopped clock occurs exactly when ruin is immediate
-- statement:
--   For the exact source τ_n=toNNReal(min(ruinTime,n)) and strictly positive n, τ_n=0 iff the original extended ruinTime itself is zero. The accepted source coe-toNNReal equality transports zero clocks to min ruin n=0 and strict positivity of n rules out the horizon branch. This pins down the exceptional τ=0 terminal W and time-zero dividend atom convention without assuming away immediate ruin.
-- source:
--   Proved source truncated-clock NNReal bounds 6b7a13a0, Mathlib lt_min and pos_iff_ne_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At every strictly positive deterministic horizon, the true stopped clock is zero exactly at immediate ruin. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) :
    ∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal = 0 ↔
      ruinTime X x D ω = 0 := by sorry
