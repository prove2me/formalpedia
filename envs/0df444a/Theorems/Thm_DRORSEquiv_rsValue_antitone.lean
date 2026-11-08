-- Prove2me | Theorems.Thm_DRORSEquiv_rsValue_antitone
-- name    : DRORSEquiv.rsValue_antitone
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T13:37:57.711328+00:00
-- url     : https://prove2.me/theorems/ea8f61b1-749e-4ca7-ab0e-2626e07a7bb4
-- title:
--   Proof of Theorem 1, p.34 — the RS value function $\kappa$ is nonincreasing
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   The RS value function is nonincreasing: if $\tau\le\tau'$ then $\kappa(\tau')\le\kappa(\tau)$.
--
--   A larger cost target relaxes the constraint of Problem (RS), so the minimal fragility can only decrease. The proof of Theorem 1 uses this to show that subgradients of $\kappa$ are nonpositive.
--
--   Differences from the source:
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.34

import Mathlib
import Definitions.Def_DRORSEquiv_rsValue

namespace DRORSEquiv

/-- **The RS value function is nonincreasing** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.34:
"Because k∗(τ) is a nonincreasing function, we have k∗(τ̂) ≥ k∗(τ̄).").

`τ ≤ τ'` implies `κ(τ') ≤ κ(τ)`. -/
theorem rsValue_antitone {E Ω : Type*} {S : ℕ} (M : Model E Ω S) : Antitone (rsValue M) := by sorry

end DRORSEquiv
