-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_residual_wait_positive_ae
-- name    : AvramDividend.Classical.avram_a06_original_residual_wait_positive_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:02:43.943136+00:00
-- url     : https://prove2.me/theorems/19f3557c-0da1-4212-b5b0-3f9280f2ffb2
-- title:
--   The original renewal residual waiting time is strictly positive almost surely
-- statement:
--   Take n equal to the original renewal count N at the fixed clock. The original almost-sure threshold equivalence forces the (n+1)st arrival time to be strictly beyond the clock, hence the residual waiting time τ(n) minus the elapsed time since the nth arrival is strictly positive. This proves the positivity needed by the Borel rectangle extension, with no stronger pointwise threshold assumption and no auxiliary process.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_residual_wait_positive_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) :
    ∀ᵐ ω ∂P,
      0 < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) := by sorry
