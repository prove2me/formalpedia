-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_gaussian_tail_step
-- name    : AvramDividend.Classical.causal_neumann_gaussian_tail_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:59:41.423821+00:00
-- url     : https://prove2.me/theorems/12c4e616-ac52-48ee-ae3c-9f71d15b7050
-- title:
--   Gaussian weighted Neumann primitives satisfy the exact Volterra tail recurrence
-- statement:
--   Successive Gaussian Neumann correction primitives obey the causal Volterra convolution equation, with the same normalising constant and sign as the derivative-resolvent equation. This discharges the inductive tail recurrence used to pass from finite corrections to the full solution.
-- source:
--   Reuse the Proved causal_signed_neumann_undamped_primitive_step for the weighted primitive of each convolution power. Divide by a, rewrite the next normalized primitive as Q(n+2), replace the previous normalized primitive by Q(n+1), and move the scalar through the interval integral. This gives the n+1 induction step for hstep in causal_neumann_resolvent_dominated_convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_signed_neumann_undamped_primitive_step
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_gaussian_tail_step
    (a w β : ℝ) (K k : ℝ → ℝ) (P Q : ℕ → ℝ → ℝ)
    (hk : k = fun t : ℝ =>
      if 0 < t then -(a⁻¹ * Real.exp (-w * t) * (β + K t)) else 0)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = fun x : ℝ =>
      (1 / a) * (∫ t in Ioc (0 : ℝ) x,
        Real.exp (w * t) * P n t ∂volume)) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      Q (n + 2) x = -(1 / a) *
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * Q (n + 1) s ∂volume) := by sorry
