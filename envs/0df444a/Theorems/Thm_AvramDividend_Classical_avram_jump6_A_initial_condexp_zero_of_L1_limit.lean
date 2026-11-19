-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_condexp_zero_of_L1_limit
-- name    : AvramDividend.Classical.avram_jump6_A_initial_condexp_zero_of_L1_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:33:14.314133+00:00
-- url     : https://prove2.me/theorems/64edbbf5-fb96-44d2-991d-f843156da44a
-- title:
--   Initial conditional expectation zero is stable under true L1 convergence
-- statement:
--   Given an L1 limit of actual integrable stopped sources whose conditional expectations given the original initial right-continuous sigma algebra vanish, the limit has conditional expectation zero. Use conditional expectation contraction in L1; unconditional zero means are insufficient. This is an independent transfer lemma for finite-activity mixed Gaussian source stopping clocks.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_initial_condexp_zero_of_L1_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (ℋ : MeasurableSpace Ω) (hℋ : ℋ ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hFI : ∀ n, Integrable (f n) P) (hGI : Integrable g P)
    (hZero : ∀ n, P[f n | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hL1 : Tendsto (fun n => eLpNorm (fun ω => g ω - f n ω) 1 P)
      atTop (nhds 0)) :
    P[g | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
