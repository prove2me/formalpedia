-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_centred_source_signed_grid_bias_expected_bound
-- name    : AvramDividend.Classical.avram_jump6_B_centred_source_signed_grid_bias_expected_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:59:12.883034+00:00
-- url     : https://prove2.me/theorems/f3a2767f-28c1-426f-bdd9-f3e09bfad257
-- title:
--   Expected original signed grid budget from exact centred martingale and vanishing Euler bias
-- statement:
--   On a probability space, if the finite physical source is the sum of a genuine mean-zero integrable centred stochastic part, an integrable nonpositive-mean generator part and a deterministic mesh discretisation bias, its expected value is bounded above by that bias at each mesh. The result is sound with nonzero finite-grid Euler bias, and can replace invalid exact mean-zero of Source minus frozen generator in the original Levy physical-grid approach.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_centred_source_signed_grid_bias_expected_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Source M Q : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hM : ∀ j, Integrable (M j) P)
    (hQ : ∀ j, Integrable (Q j) P)
    (hMzero : ∀ j, (∫ ω, M j ω ∂P) = 0)
    (hQmean : ∀ j, (∫ ω, Q j ω ∂P) ≤ 0)
    (hSource : ∀ j ω,
      Source j ω = M j ω + Q j ω + bias j) :
    ∀ j, (∫ ω, Source j ω ∂P) ≤ bias j := by sorry
