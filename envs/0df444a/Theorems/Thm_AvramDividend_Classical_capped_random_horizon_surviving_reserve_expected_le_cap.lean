-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_random_horizon_surviving_reserve_expected_le_cap
-- name    : AvramDividend.Classical.capped_random_horizon_surviving_reserve_expected_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:06:29.029281+00:00
-- url     : https://prove2.me/theorems/c252e88b-368f-41cc-9d33-e4334900ae42
-- title:
--   Expected surviving controlled reserve is capped even at a path-dependent localisation time
-- statement:
--   For every path-dependent nonnegative horizon τ, including values τ=0, restrict the controlled reserve to sample paths on which τ precedes ruin. If the strategy is capped and the initial capital is in the cap, its extended-real expected surviving reserve is at most C. The pathwise cap-domain lemma handles positive and zero times; monotonicity of the nonnegative integral and the probability normalisation give the expected bound. This is suitable for terminal-value estimates at stochastic localisation horizons, though stopped-process measurability and Itô's formula still require independent justification.
-- source:
--   The canonically Proved capped_riskProcess_range_before_ruin_including_zero once accepted; the Prove2Me spectrally negative Lévy and capped admissibility definitions, and Mathlib.MeasureTheory.Integral.Lebesgue.Basic.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_random_horizon_surviving_reserve_expected_le_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) :
    (∫⁻ ω, if ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      ENNReal.ofReal (riskProcess X x D (τ ω) ω) else 0 ∂P) ≤ C := by sorry
