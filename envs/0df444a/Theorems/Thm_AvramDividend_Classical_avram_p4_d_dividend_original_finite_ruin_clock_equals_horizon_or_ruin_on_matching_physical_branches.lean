-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_ruin_clock_equals_horizon_or_ruin_on_matching_physical_branches
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_clock_equals_horizon_or_ruin_on_matching_physical_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:05:47.717725+00:00
-- url     : https://prove2.me/theorems/79de8c71-798f-480e-a604-921b36fddb4a
-- title:
--   Original finite controlled stop equals the horizon or ruin on the corresponding source branch
-- statement:
--   At literal source tau=min(ruinTime,n).toNNReal, show tau=n whenever finite horizon n≤ruinTime and tau=ruinTime whenever the controlled ruin occurs by n. Includes equal ruin/horizon and infinite ruin paths. These identities provide exact original right-horizon versus terminal-ruin reconciliation for the closed Stieltjes cash budget.
-- source:
--   Proved P4-D original exact extended-time clock equality and Mathlib min_eq_left/min_eq_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_finite_ruin_clock_equals_horizon_or_ruin_on_matching_physical_branches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω,
      ((n : ℝ≥0∞) ≤ ruinTime X x D ω →
        (τ ω : ℝ≥0∞) = (n : ℝ≥0∞)) ∧
      (ruinTime X x D ω ≤ (n : ℝ≥0∞) →
        (τ ω : ℝ≥0∞) = ruinTime X x D ω) := by sorry
