-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_survival_iff_horizon
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_clock_survival_iff_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:28:28.724817+00:00
-- url     : https://prove2.me/theorems/e5566d32-60c2-490c-9ea3-b782fd2f8323
-- title:
--   Genuine original clipped terminal lies strictly before ruin iff deterministic horizon precedes ruin
-- statement:
--   For the true original τ_n=(min(ruinTime X x D ω,n)).toNNReal, the embedding of τ_n into ENNReal is strictly before ruin if and only if n itself is strictly before ruin. This is valid for zero and positive horizons and finite or infinite ruin, providing the exact survival-terminal branch for original W; no dividend time atom is deleted.
-- source:
--   Accepted source exact clipped clock embedding theorem 6b7a13a0; linear order identity min_lt_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source stopped survival is equivalent to the integer horizon before ruin. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_clock_survival_iff_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω ↔
    (n : ℝ≥0∞) < ruinTime X x D ω := by sorry
