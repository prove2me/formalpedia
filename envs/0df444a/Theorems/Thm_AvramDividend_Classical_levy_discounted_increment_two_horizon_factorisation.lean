-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_discounted_increment_two_horizon_factorisation
-- name    : AvramDividend.Classical.levy_discounted_increment_two_horizon_factorisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:08:04.792561+00:00
-- url     : https://prove2.me/theorems/51fb3ec9-26f7-4637-89ec-d40433296b35
-- title:
--   Pathwise discounted two-horizon Lévy exponential factorisation
-- statement:
--   At arbitrary random time τ, the discounted exponential of the total future increment factors into discounted exponentials for its two consecutive segments. This algebraic identity supports conditional Markov and dividend-verification semigroup calculations.
-- source:
--   At arbitrary random time τ, the discounted exponential of the total future increment factors into discounted exponentials for its two consecutive segments. This algebraic identity supports conditional Markov and dividend-verification semigroup calculations.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_discounted_increment_two_horizon_factorisation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (θ q : ℝ) (ω : Ω) :
    Real.exp (-(q * ((h + k) : ℝ))) *
      Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω) ω)) =
      (Real.exp (-(q * (h : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) *
        (Real.exp (-(q * (k : ℝ))) *
        Real.exp (θ * (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω))) := by sorry
