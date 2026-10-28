-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_two_horizon_exponential_factorisation
-- name    : AvramDividend.Classical.levy_increment_two_horizon_exponential_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:04:06.878498+00:00
-- url     : https://prove2.me/theorems/d93899ca-ddfe-4ee0-8335-8ddbe1ccea30
-- title:
--   Pathwise factorisation of the exponential two-horizon Lévy increment
-- statement:
--   Use the pathwise telescoping identity for a two-horizon increment, distribute the Laplace parameter over the sum, and apply exp(a+b)=exp(a)exp(b). This factorisation is independent of optional stopping and is reusable in conditional Markov calculations.
-- source:
--   Use the pathwise telescoping identity for a two-horizon increment, distribute the Laplace parameter over the sum, and apply exp(a+b)=exp(a)exp(b). This factorisation is independent of optional stopping and is reusable in conditional Markov calculations.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_increment_two_horizon_exponential_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (θ : ℝ) (ω : Ω) :
    Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) =
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω)) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) := by sorry
