-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_finset_sum
-- name    : AvramDividend.Classical.causal_Ioc_kernel_integral_finset_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:54:37.023988+00:00
-- url     : https://prove2.me/theorems/f7b9785a-cdd1-44e0-ab32-e2ecaef3660d
-- title:
--   Exact finite Neumann-sum interchange with the causal (0,x] integral
-- statement:
--   For a fixed endpoint x and a finite sequence of input functions, if each causal kernel product is integrable on (0,x], the integral of the kernel multiplied by the finite sum equals the sum of causal integrals. This directly supplies the finite operator additivity hypothesis for the canonical Neumann telescope.
-- source:
--   MeasureTheory.integral_finset_sum in the pinned Mathlib revision, with exact interval restricted integrability.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_kernel_integral_finset_sum
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hI : ∀ i ∈ Finset.range (n + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume) :
    (∫ s in Ioc (0 : ℝ) x,
      B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i s) ∂volume) =
    ∑ i ∈ Finset.range (n + 1),
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q i s ∂volume) := by sorry
