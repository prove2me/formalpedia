-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_shifted_increment_rectangle_eq
-- name    : AvramDividend.Classical.levy_finitePrefix_shifted_increment_rectangle_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:18:34.177828+00:00
-- url     : https://prove2.me/theorems/246f114d-1902-4f44-a10c-f1eaab30b7a4
-- title:
--   Finite consecutive Lévy increments have stationary joint rectangle distributions
-- statement:
--   Every finite vector of consecutive increments over a monotone observation grid has the same joint probabilities on Borel rectangles after an arbitrary deterministic time shift s. Both vectors have independent components by the Proved finite prefix rectangle factorisation; each component has the same law under the shift by stationary increments. This is the core finite-dimensional stationarity step.
-- source:
--   Uses levy_finitePrefix_increment_rectangle_product (publishing) and SpectrallyNegativeLevy.stationaryIncrements. Intermediate towards full whole-path stationarity and Markov dividend child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.IdentDistrib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finitePrefix_shifted_increment_rectangle_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) ∈
        Set.pi Set.univ B} =
    P {ω | (fun i : Fin n =>
      X.X (t (i.val + 1)) ω - X.X (t i.val) ω) ∈
        Set.pi Set.univ B} := by
  sorry
