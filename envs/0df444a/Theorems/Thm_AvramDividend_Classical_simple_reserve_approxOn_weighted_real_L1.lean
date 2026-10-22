-- Prove2me | Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_weighted_real_L1
-- name    : AvramDividend.Classical.simple_reserve_approxOn_weighted_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:09:49.260695+00:00
-- url     : https://prove2.me/theorems/e54b5c31-ee28-482d-a698-e9fbf0766167
-- title:
--   Scaled ordinary-L1 convergence for canonical simple reserve approximations
-- statement:
--   For an integrable measurable real reserve Z and any real scaling constant L, the integral of L times the absolute difference between its canonical Mathlib SimpleFunc.approxOn approximation and Z tends to zero. Apply the already Proved ordinary-L1 convergence theorem and the exact Mathlib integral_const_mul identity. This supplies the weighted L1 convergence premise used for Lipschitz conditional Markov stability, including the relevant nonnegative Lipschitz constants.
-- source:
--   Accepted simple_reserve_approxOn_real_L1 target 581ebb8d-397f-4033-a648-e30738a53c27. Pinned declaration oracle confirms MeasureTheory.integral_const_mul.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_real_L1

open Filter MeasureTheory Set

theorem AvramDividend.Classical.simple_reserve_approxOn_weighted_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hI : Integrable Z P) (L : ℝ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, L * |(SimpleFunc.approxOn Z hZ
          (Set.range Z ∪ {0}) 0 (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by sorry
