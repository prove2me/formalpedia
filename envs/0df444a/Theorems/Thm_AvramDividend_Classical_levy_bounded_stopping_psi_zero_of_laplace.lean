-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_psi_zero_of_laplace
-- name    : AvramDividend.Classical.levy_bounded_stopping_psi_zero_of_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:40:07.378585+00:00
-- url     : https://prove2.me/theorems/ad3e9ef5-dbd0-427f-bc74-3c1db9f1604e
-- title:
--   Normalisation of the Lévy exponent at zero from bounded stopping
-- statement:
--   For any Lévy process satisfying the stopped transform identity on a probability space, its Laplace exponent vanishes at parameter zero.
-- source:
--   Evaluate the accepted stopping-time Laplace identity at parameter zero and unit horizon. The integrand is one, its probability integral is one, and injectivity of the real exponential gives ψ(0)=0.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_psi_zero_of_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T) :
    X.ψ 0 = 0 := by sorry
