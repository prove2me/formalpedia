-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_head_tail_global_step
-- name    : AvramDividend.Classical.causal_neumann_head_tail_global_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:06:42.746394+00:00
-- url     : https://prove2.me/theorems/4965af00-4891-4ec3-8b0c-e300d7eacab0
-- title:
--   Positive Gaussian head and tail recurrences extend to the full causal operator
-- statement:
--   A Gaussian Neumann sequence satisfying its initial and subsequent convolution recurrences for positive times, and vanishing after its constant term for nonpositive times, obeys the complete causal Volterra operator equation as an identity of functions on all real arguments.
-- source:
--   Split n into zero and successor and x into positive and nonpositive cases. The Proved head and tail Gaussian primitive recurrences supply the positive cases; the nonpositive zero-extension lemma and Ioc_eq_empty_of_le supply the remaining cases. This gives the exact whole-function hstep argument of causal_neumann_resolvent_dominated_convergence.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_head_tail_global_step
    (a : ℝ) (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hhead : ∀ x : ℝ, 0 < x →
      Q 1 x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q 0 s ∂volume))
    (htail : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      Q (n + 2) x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q (n + 1) s ∂volume))
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0) :
    ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)) := by sorry
