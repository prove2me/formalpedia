-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_physmask_event_cell_centred_sum
-- name    : AvramDividend.Classical.avram_b27_original_physmask_event_cell_centred_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:14:13.958198+00:00
-- url     : https://prove2.me/theorems/c9dd57a6-550b-404e-92cc-6e59aae3f684
-- title:
--   Original ruin-clipped physical mesh gains have zero restricted mean when every stopped cell is centred
-- statement:
--   For the exact bounded-predictable source mesh syntax used by Avram B25, including the original stopped mask if sigma<=a_i then 0, if every individual masked increment is integrable and has zero mean on a specified measurable event A, then the finite sum has zero mean on A. The event may be the no-large-jump Poisson event. This isolates the true cellwise conditional-centering obligation in the B25 Brownian plus negative compound-Poisson obstruction without replacing the original ruin stopping clock.
-- source:
--   Avram B25 original physical two-channel source, theorem 78ac3aee; event obstruction audit 15 November 2026. Bochner integral finset additivity for integrable stopped mesh gains.

import Mathlib
open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.avram_b27_original_physmask_event_cell_centred_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω)
    (σ : Ω → ℝ≥0) (R : ℝ≥0 → Ω → ℝ)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (W : ℕ → Ω → ℝ)
    (hCellInt : ∀ i ∈ S,
      Integrable (fun ω =>
        (if σ ω ≤ a i then 0 else W i ω) *
          (R (b i) ω - R (a i) ω)) (P.restrict A))
    (hCellMean : ∀ i ∈ S,
      (∫ ω in A,
        (if σ ω ≤ a i then 0 else W i ω) *
          (R (b i) ω - R (a i) ω) ∂P) = 0) :
    (∫ ω in A, ∑ i ∈ S,
      (if σ ω ≤ a i then 0 else W i ω) *
        (R (b i) ω - R (a i) ω) ∂P) = 0 := by sorry
