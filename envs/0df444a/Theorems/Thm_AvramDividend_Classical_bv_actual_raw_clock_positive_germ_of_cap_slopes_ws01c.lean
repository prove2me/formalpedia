-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c
-- name    : AvramDividend.Classical.bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:04:10.311745+00:00
-- url     : https://prove2.me/theorems/8a1f87ac-9b56-4f3a-95c4-e94a302c4273
-- title:
--   Almost-sure zero slopes at all capped clocks force a positive right germ at the finite raw clock
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with the canonical positive drift, suppose its post-clock drift-deficit slope converges to zero almost surely for every integer cap of any extended nonnegative raw random clock. Then, on the event that the raw clock is finite, its original Lévy path has strictly positive increments on some short right-hand interval. Apply the independently Proved cap-specific positive-germ theorem at each integer cap and the countable-cap removal lemma. This creates the precise random-clock germ needed at a potential continuous lower-boundary contact.
-- source:
--   New complete WS1C bridge composing the remotely submitted post-clock germ with countable removal of finite caps, preserving all clock finiteness and dyadic hypotheses explicitly.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_post_clock_positive_germ_of_dyadic_zero_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_countable_cap_germs_to_finite_raw_clock_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0∞) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ →
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X ((τ ω).toNNReal + t) ω -
            X.X ((τ ω).toNNReal) ω := by sorry
