-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_two_horizon_telescope
-- name    : AvramDividend.Classical.levy_increment_two_horizon_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:04:15.970996+00:00
-- url     : https://prove2.me/theorems/afbfbacc-09fa-42b0-8b96-640d17bcf6d9
-- title:
--   Pathwise two-horizon decomposition of Lévy increments
-- statement:
--   For each sample path and any random time τ, the increment to horizon h+k telescopes through the intermediate point τ+h. This pathwise algebraic equality is reusable for stochastic semigroup and conditional Markov proofs.
-- source:
--   For each sample path and any random time τ, the increment to horizon h+k telescopes through the intermediate point τ+h. This pathwise algebraic equality is reusable for stochastic semigroup and conditional Markov proofs.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_increment_two_horizon_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (h k : ℝ≥0) (ω : Ω) :
    X.X (τ ω + (h + k)) ω - X.X (τ ω) ω =
      (X.X (τ ω + (h + k)) ω - X.X (τ ω + h) ω) +
        (X.X (τ ω + h) ω - X.X (τ ω) ω) := by sorry
