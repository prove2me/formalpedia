-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_integral_resolvent_of_convergence
-- name    : AvramDividend.Classical.causal_neumann_integral_resolvent_of_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:12:23.050935+00:00
-- url     : https://prove2.me/theorems/fd8e5448-459b-4806-b29e-9eaf0204f6d8
-- title:
--   Infinite causal Volterra Neumann series solves its resolvent equation
-- statement:
--   Given a signed Neumann sequence with the native causal integral recursion and integrability, suppose its finite partial sums converge pointwise to g, the causal integrals of those partial sums converge to the causal integral of g, and the final remainder vanishes. The limiting function then solves g+(1/a)B*g=F at every real x. These are exactly the analytic convergence premises of the Gaussian derivative-resolvent construction.
-- source:
--   Compose canonical finite causal integral telescope and convergence-of-finite-resolvent theorem.

import Mathlib.Topology.Defs.Filter
import Theorems.Thm_AvramDividend_Classical_causal_neumann_finite_integral_telescope
import Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_identity_of_finite_convergence

open AvramDividend.Classical MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_neumann_integral_resolvent_of_convergence
    (a : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (hS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)))
    (hTS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (1 / a) * (∫ s in Ioc (0 : ℝ) x,
        B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s ∂volume))
      atTop (nhds ((1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume))))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ))) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by sorry
