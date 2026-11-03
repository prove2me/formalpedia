-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
-- name    : AvramDividend.Classical.avram_wave7_08_source_truncated_clock_nnreal_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:22:00.636769+00:00
-- url     : https://prove2.me/theorems/6b7a13a0-fa75-494d-8d56-b14562c66491
-- title:
--   Original Avram min-ruin finite clock has an exact bounded NNReal representation
-- statement:
--   For the actual original source ruinTime X x D and every deterministic natural clock n, converting min(ruinTime,n) to ℝ≥0 using ENNReal.toNNReal preserves the exact ENNReal clock; the resulting time is at most n and at most actual ruinTime. This supplies the two exact deterministic stopping-clock bound hypotheses required by the already Proved original one-sided HJB expected-budget theorem, leaving the filtration stopping-time proof and mixed-jump Ito identity separate.
-- source:
--   Exact canonical original source clock normalization, no substitution of Ω/P/X/D. Pinned Mathlib ENNReal.coe_toNNReal and ENNReal.coe_le_coe at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_truncated_clock_nnreal_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    let τ : Ω → ℝ≥0 :=
      fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∀ ω, (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (n : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ (n : ℝ≥0)) ∧
    (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by sorry
