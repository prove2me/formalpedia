-- Prove2me | Theorems.Thm_DRORSEquiv_subgradient_neg
-- name    : DRORSEquiv.subgradient_neg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:15.197552+00:00
-- url     : https://prove2.me/theorems/605aa14e-84f4-40b5-a637-e364ff38df1c
-- title:
--   Proof of Theorem 1, p.34 — $0\notin\partial\kappa(\tau_{rs})$ and every subgradient is negative for $\tau_{rs}<\bar\tau$ (corrected: RS($\tau_{rs}$) has an optimal solution)
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose $S\ge1$, $\bar\tau=t$ is finite, $Z_0\le\tau_{rs}<t$, and Problem (RS) with target $\tau_{rs}$ has an optimal solution. Then
--
--   $$0\notin\partial\kappa(\tau_{rs})\qquad\text{and}\qquad\alpha<0\ \text{ for every }\alpha\in\partial\kappa(\tau_{rs}).$$
--
--   Hence $\theta^*=-1/\alpha$ is a well-defined positive radius for every subgradient $\alpha$ at a target strictly below the robust optimum.
--
--   Differences from the source:
--   - correction: 0 ∉ ∂k*(τrs) for any τrs ∈ (Z0, τ̄) → assumes RS(τrs) has an optimal solution; reason: without it the claim fails: X = [0, ∞), f(x, z) = max(0, 1 − x/|z|) for z ≠ 0, f(x, 0) = 0, Z = ℝ, ρ = |·|, S = 1, ẑ₁ = 0 give κ ≡ 0 on [0, ∞) unattained, so 0 ∈ ∂κ(1/2); the page's "Since k∗(τ̂) = 0, the first constraint in the problem RS(τ̂) indicates …" uses an attained k = 0
--   - generalization: τrs in the open interval (Z0, τ̄) → Z0 ≤ τrs < τ̄; reason: the open interval is a special case
--   - generalization: the setting of Theorem 1 (X convex, f convex in x, Polish (Z, ρ), f ∈ L¹, bounded growth) → no convexity and no measure-level assumptions; reason: the sign follows from κ = 0 on (τ̄, ∞) and κ(τrs) > 0; the paper's instances satisfy the weaker hypotheses
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.34

import Mathlib
import Definitions.Def_DRORSEquiv_IsRSOptimal
import Definitions.Def_DRORSEquiv_rsValue
import Definitions.Def_DRORSEquiv_subdiff
import Definitions.Def_DRORSEquiv_empiricalOptimum
import Definitions.Def_DRORSEquiv_tauBar

namespace DRORSEquiv

/-- **`0 ∉ ∂κ(τrs)` and every subgradient is negative** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of
Theorem 1, p.34: "Next, we show that 0 ∉ ∂k∗(τrs) for any τrs ∈ (Z0, τ̄)." and "Hence we can get θ∗ by
letting θ∗ = −1/α, where α ∈ ∂k∗(τrs). We claim that α < 0.").

Suppose `τ̄ = t` is finite, `Z₀ ≤ τrs < t`, and RS(τrs) has an optimal solution. Then `0 ∉ ∂κ(τrs)` and
every `α ∈ ∂κ(τrs)` satisfies `α < 0`.

**Formalization Note.** Corrected: an optimal solution of RS(τrs) is assumed. Without it the claim fails
(`X = [0, ∞)`, `f(x, z) = max(0, 1 − x/|z|)` for `z ≠ 0`, `f(x, 0) = 0`, `Z = ℝ`, `ρ = |·|`, `ẑ₁ = 0`:
`κ ≡ 0` on `[0, ∞)` unattained, so `0 ∈ ∂κ(1/2)`); the page's "Since k∗(τ̂) = 0, the first constraint in
the problem RS(τ̂) indicates …" uses an attained `k = 0`. Generalization: the closed left end `Z₀ ≤ τrs`
(the page has the open interval). -/
theorem subgradient_neg {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (hS : 0 < S)
    (t : ℝ) (ht : tauBar M = (t : EReal)) (τrs : ℝ)
    (hlo : empiricalOptimum M ≤ (τrs : EReal)) (hlt : τrs < t)
    (x : E) (k : ℝ) (hopt : IsRSOptimal M τrs x k) :
    (0 : ℝ) ∉ subdiff (rsValue M) τrs ∧ ∀ α ∈ subdiff (rsValue M) τrs, α < 0 := by sorry

end DRORSEquiv
