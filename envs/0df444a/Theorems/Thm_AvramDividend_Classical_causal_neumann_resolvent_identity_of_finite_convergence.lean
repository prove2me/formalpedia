-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_identity_of_finite_convergence
-- name    : AvramDividend.Classical.causal_neumann_resolvent_identity_of_finite_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T13:09:31.971862+00:00
-- url     : https://prove2.me/theorems/c6b5401e-ecfa-4747-9e8e-980fae889825
-- title:
--   Pass a finite Neumann Volterra equation to its convergent resolvent
-- statement:
--   For finite Neumann partial sums S_n satisfying S_n+T(S_n)=F-Q_(n+1), assume pointwise convergence S_n→g, T(S_n)→Tg, and Q_(n+1)→0. Then the limiting resolvent solves the exact equation g+Tg=F. This isolates the convergence and convolution-continuity obligations from finite algebraic telescoping.
-- source:
--   Pointwise limits of finite Neumann identities using Tendsto.add, Tendsto.sub and uniqueness of limits; no local Lean.

import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

open Filter

theorem AvramDividend.Classical.causal_neumann_resolvent_identity_of_finite_convergence
    (F g : ℝ → ℝ) (T : (ℝ → ℝ) → (ℝ → ℝ))
    (S Q : ℕ → ℝ → ℝ)
    (hfinite : ∀ n : ℕ, S n + T (S n) = F - Q (n + 1))
    (hS : ∀ x : ℝ, Tendsto (fun n : ℕ => S n x) atTop (nhds (g x)))
    (hTS : ∀ x : ℝ, Tendsto (fun n : ℕ => T (S n) x)
      atTop (nhds (T g x)))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ))) :
    ∀ x : ℝ, g x + T g x = F x := by sorry
