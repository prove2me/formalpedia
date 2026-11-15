-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- name    : AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:16:54.085444+00:00
-- url     : https://prove2.me/theorems/f4b58008-0b90-457b-b302-a1d4aa180f90
-- title:
--   Original finite-activity actual physical causal negative jump sum has exactly the compound Poisson Laplace functional
-- statement:
--   At a fixed horizon, the actual causal sum over physical original negative Lévy jumps has Laplace transform exp(t ∫_{(-∞,0)} (e^{θy}-1) ν(dy)), for every positive tilt. It depends only on X and the marked jump measure ν, without any Gaussian companion or raw Gaussian independence. The assertion is invariant under measurable a.e. representatives of the actual physical sum. This is the exact compound-Poisson component required to close A72 using the deterministic finite-activity Lévy exponent split A76.
-- source:
--   Finite negative-jump Poisson random measure on the actual original Levy source; Proved original bounded physical count moments and original finite marked jump support, original negative-band PGFs, marked simple weight quantisation; Avram–Palmowski–Pistorius 2007 Levy-Khintchine finite activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a77_original_finite_activity_physical_negative_jump_compound_poisson_laplace_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) :
    (∫ ω, Real.exp (θ * J ω) ∂P) =
      Real.exp ((t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) := by sorry
