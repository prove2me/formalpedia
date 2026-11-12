-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
-- name    : AvramDividend.Classical.avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:11:21.847622+00:00
-- url     : https://prove2.me/theorems/959ce01a-348d-42a3-b95b-69ffa2dfc936
-- title:
--   L2 convergence on a probability space controls eventwise absolute L1 error
-- statement:
--   If f_n converges to g in L2(P), then the expected |g-f_n| on any event A tends to zero, by Lp exponent comparison, real lpNorm identity and restriction monotonicity.
-- source:
--   Reusable abstract completion of the linear grid L2-Cauchy bridge gb30 to gb23; also applies to quadratic gb28 to gb24.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb29_probabilistic_L2_to_eventwise_L1_transfer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 P) (hg : MemLp g 2 P)
    (hL2 : Tendsto (fun n : ℕ => eLpNorm (f n - g) 2 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun n : ℕ => ∫ ω in A, |g ω - f n ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
