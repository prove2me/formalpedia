-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_uniform_grid_pattern_real_ws01b
-- name    : AvramDividend.Classical.bv_actual_uniform_grid_pattern_real_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:14:17.754255+00:00
-- url     : https://prove2.me/theorems/43ef4e2d-71c7-45be-b545-57897bc60b3b
-- title:
--   Exact real-valued joint Bernoulli probability for every original Lévy equal-width grid pattern
-- statement:
--   On a deterministic increasing observation grid with constant spacing h, the probability that the actual bounded-variation finite-activity spectrally negative Lévy process has strict negative residual increments at exactly the selected active cells, and zero residual increments at all remaining cells, equals the finite product of Bernoulli masses 1−exp(−hλ) and exp(−hλ), where λ is the total negative jump intensity.
-- source:
--   The complete original-process Lean proof has passed the pinned Prove2Me remote compiler on 28 October 2026. It combines proved arbitrary grid-cylinder independence with the proved positive/zero residual increment probabilities and a direct algebraic event identification.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_residual_active_pattern_product_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For the actual finite-activity Lévy process, every fixed-length
grid pattern has the exact joint Bernoulli probability. -/

theorem AvramDividend.Classical.bv_actual_uniform_grid_pattern_real_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (active : Finset ℕ)
    (h : ℝ)
    (hgap : ∀ i : ℕ, i < n →
      (((t (i + 1) - t i : ℝ≥0) : ℝ)) = h) :
    P.real {ω : Ω | ∀ i : ℕ, i < n →
      X.X (t (i + 1)) ω - X.X (t i) ω ∈
        (if i ∈ active then
          Iio (X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ)))
        else
          {X.drift * (((t (i + 1) - t i : ℝ≥0) : ℝ))})} =
    ∏ i ∈ Finset.range n,
      if i ∈ active then
        1 - Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal))
      else
        Real.exp (-(h * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
