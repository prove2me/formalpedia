-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_theorem_1
-- name    : DriftVarCtrl.FixedLB.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:40.967263+00:00
-- url     : https://prove2.me/theorems/48b12ec5-79f8-41f7-9c2a-e709482329b0
-- title:
--   Theorem 1, p. 10 — an at-most-two-interval policy is optimal; off (h*₁, h*₂) every optimal interval policy has at most two intervals
-- statement:
--   Consider the two-control drift–variance problem on $[0,U]$ with drifts $\mu_i > 0$, volatilities $\sigma_i > 0$, costs $h_i > 0$, terminal cost $M < 0$ at $U$ and $0$ at $0$, and assume $v_1 < v_2$, where $v_i = 2\mu_i/\sigma_i^2$. Then:
--   1. there is an optimal interval policy with at most two intervals;
--   2. if $(h_1,h_2) \ne (h_1^*,h_2^*)$, where $h_i^* = -M\mu_i/U$, then every optimal interval policy has at most two intervals.
--
--   In the paper's words, "The optimal policy is at most a two-interval policy": the entrepreneur either uses one control throughout or switches between the two controls exactly once.
--
--   **Formalization Note.** Policies are the $k$-interval policies of Definition 1, to which the paper restricts (p. 8). A policy's value is its analytic value: the $C^1$ function on $[0,U]$ with $W(0) = 0$, $W(U) = M$ that solves the policy's ODE $h_i + \mu_iW' + \frac{\sigma_i^2}{2}W'' = 0$ on each piece. The identification with the expected cost (2) (Dynkin's formula) is not formalized. The standing $v_1 < v_2$ (p. 12) is the hypothesis `hv`. Part 2 excludes the critical point $(h_1,h_2) = (h_1^*,h_2^*)$, i.e. $\Delta h_1 = \Delta h_2 = 0$: there the affine function $Mx/U$ solves both ODEs, it is the value of every interval policy, and every policy (of any length) is optimal, so the paper's uniqueness argument fails at that point.
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 10, Theorem 1 (proof p. EC-14)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model

namespace DriftVarCtrl.FixedLB

/-- Theorem 1 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 10; proof p. EC-14). "The optimal policy is at most a two-interval policy":
(i) some interval policy with at most two intervals is optimal; (ii) unless `(h₁, h₂) = (h*₁, h*₂)`,
every optimal interval policy has at most two intervals.

Formalization Note: policies are the paper's k-interval policies (Definition 1, pp. 8–9), to which
the paper restricts (p. 8). A policy's value is the analytic `IsValue` (the policy's ODE system with
`W(0) = 0`, `W(U) = M` and `C¹` pasting), not the expected cost (2): the identity between them
(Dynkin's formula, Lemma 12) is not formalized. `L = m = 0`, `M < 0`, cost minimization (p. 8). The
standing `v₁ < v₂` (p. 12) is the hypothesis `hv`. Part (ii) carries the hypothesis
`¬(Δh₁ = 0 ∧ Δh₂ = 0)`: at `(h₁, h₂) = (h*₁, h*₂)` the affine function `Mx/U` is the value of every
interval policy, so every policy is optimal and the printed uniqueness claim fails there. -/
theorem theorem_1 (p : Params) (hv : v p .one < v p .two) :
    (∃ π : IntervalPolicy p, π.k ≤ 2 ∧ IsOptimal p π) ∧
    (¬ (Δh p .one = 0 ∧ Δh p .two = 0) →
      ∀ π : IntervalPolicy p, IsOptimal p π → π.k ≤ 2) := by sorry

end DriftVarCtrl.FixedLB
