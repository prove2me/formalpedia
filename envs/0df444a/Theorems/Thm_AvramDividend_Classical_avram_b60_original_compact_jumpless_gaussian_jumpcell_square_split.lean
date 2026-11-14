-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
-- name    : AvramDividend.Classical.avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:27:33.2571+00:00
-- url     : https://prove2.me/theorems/0bf8d88f-bdff-46e5-bbc9-89e15f693680
-- title:
--   Original compact physical increments split into Gaussian-drift quadratic energy and negative jump-cell count
-- statement:
--   For actual original Lévy path increments on any finite collection of physical intervals, suppose that on the no-negative-source-jump cells the drift-corrected increment equals a genuine Gaussian residual plus a specified deterministic drift correction, and on the jump-bearing cells its absolute value is bounded by the width of the compact spatial band. Then the sum of the true squared drift-corrected source increments is bounded samplewise by twice the Gaussian quadratic energy plus twice the drift-square duration energy plus the band-width square per jump-bearing cell. This holds for arbitrary finite grids, without fixed cardinality and without any negative-jump second moment.
-- source:
--   Physical source path increment split under explicit no-jump decomposition and compact jump-contact hypotheses, elementary square-comparison algebra; intended to combine with B58 original jump-cell expected count and original Gaussian martingale bracket energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (A : Set Ω) (d a b : ℝ) (hab : a ≤ b)
    (hNoJump : ∀ ω ∈ A, ∀ i ∈ S, i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω ∈ A, ∀ i ∈ S, i ∈ J ω →
      |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a) :
    ∀ ω ∈ A,
      (∑ i ∈ S,
        (X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2) ≤
      ∑ i ∈ S,
        (2 * (V i ω)^2 +
          2 * d^2 * (((t i ω - s i ω : ℝ≥0) : ℝ))^2 +
          if i ∈ J ω then (b-a)^2 else 0) := by sorry
