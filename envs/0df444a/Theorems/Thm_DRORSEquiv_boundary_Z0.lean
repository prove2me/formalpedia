-- Prove2me | Theorems.Thm_DRORSEquiv_boundary_Z0
-- name    : DRORSEquiv.boundary_Z0
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:43.926444+00:00
-- url     : https://prove2.me/theorems/af200219-f703-43a0-a390-f7f1c7fe26c3
-- title:
--   Proof of Theorem 1, p.33 — boundary case $\tau_{rs}=Z_0$: RS($Z_0$) optima are DRO(0) optima (corrected: RS($Z_0$) may be infeasible)
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose the samples lie in $\mathcal Z$ and $\rho(z,z)=0$. Let $Z_0=\tau_0$ be finite and let $(x^*,k^*)$ be an optimal solution of RS($\tau_0$). Then
--
--   1. $x^*\in\mathcal X$ minimizes the empirical cost: $\frac1S\sum_s f(x^*,\hat z_s)\le\frac1S\sum_s f(x,\hat z_s)$ for all $x\in\mathcal X$;
--   2. $(\tau_0,k^*,x^*)$ is an optimal solution of DRO(0);
--   3. every optimal solution $(\tau',k',x')$ of DRO(0) has $\tau'=\tau_0$ and $x'$ a minimizer of the empirical cost over $\mathcal X$.
--
--   This is the left boundary of Theorem 1: at the target $Z_0$ the radius $\theta^*=0$ works, and DRO(0) is sample average approximation.
--
--   Differences from the source:
--   - correction: the empirical minimizer x* is the optimal solution of RS(Z0), and RS(Z0) and DRO(0) have the same optimal solution x* → every optimal solution (x*, k*) of RS(Z0) has x* an empirical minimizer and (Z0, k*, x*) optimal for DRO(0); every DRO(0) optimum has level Z0 and an empirical minimizer as decision; reason: RS(Z0) can be infeasible: f(x, z) = √|z|, Z = [−1, 1], ρ = |·|, S = 1, ẑ₁ = 0 give Z0 = 0 and h(x, k) = 1/(4k) for k ≥ 1/2, 1 − k for k ≤ 1/2, never ≤ 0
--   - reading: x* = arg min_{x∈X} (1/S) Σ_s f(x, ẑ_s) (a unique minimizer) → any minimizer of the empirical cost over X; reason: the page's "equality holds only when x = x*" presumes uniqueness; with a unique minimizer the two agree
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - reading: samples ẑ_s of the support (implicit), S the number of samples → hypotheses ∀ s, ẑ_s ∈ Z (and 0 < S where used); reason: implicit in the paper: the empirical distribution P† is the centre of the Wasserstein ball and lies in P(Z); every instance of the paper satisfies it
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33 (case τrs = Z0)

import Mathlib
import Definitions.Def_DRORSEquiv_IsRSOptimal
import Definitions.Def_DRORSEquiv_IsDROOptimal
import Definitions.Def_DRORSEquiv_empiricalOptimum

namespace DRORSEquiv

/-- **Boundary case `τrs = Z₀`** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33: "When
τrs = Z0, we first show that the problem RS(Z0) and DRO(0) have the same optimal solution x∗, where
x∗ = arg min_{x∈X} 1/S ∑_{s∈[S]} f(x, ẑs). […] Thus, x∗ is the optimal solution to the problem RS(Z0).
For the problem DRO(0), it reduces to the empirical optimization, and, by definition, its optimal
solution is also x∗.").

If `Z₀ = τ₀` is finite and `(x*, k*)` is an optimal solution of RS(τ₀), then `x*` minimizes the
empirical cost `(1/S) ∑_s f(·, ẑ_s)` over `X`, `(τ₀, k*, x*)` is optimal for DRO(0), and every optimal
solution `(τ', k', x')` of DRO(0) has `τ' = τ₀` and `x'` a minimizer of the empirical cost over `X`.

**Formalization Note.** Corrected: the page also claims that the empirical minimizer is optimal for
RS(Z₀), which fails when RS(Z₀) is infeasible (`f(x, z) = √|z|`, `Z = [−1, 1]`, `S = 1`, `ẑ₁ = 0`:
`h(x, k) > 0 = Z₀` for all `k`). The statement keeps what holds: RS(Z₀) optima are DRO(0) optima, and both have an empirical minimizer as
their `x`-component (the page's "arg min" presumes a unique minimizer; any minimizer is allowed here). The
samples lie in `Z` and `ρ(z, z) = 0` (implicit in the paper: `P†` is the centre of the ball). -/
theorem boundary_Z0 {E Ω : Type*} {S : ℕ} (M : Model E Ω S)
    (hzhat : ∀ s, M.zhat s ∈ M.Z) (hρ0 : ∀ z, M.ρ z z = 0)
    (τ₀ : ℝ) (hZ0 : empiricalOptimum M = (τ₀ : EReal)) (x : E) (k : ℝ)
    (hopt : IsRSOptimal M τ₀ x k) :
    (x ∈ M.X ∧ ∀ x' ∈ M.X,
        (1 / (S : ℝ)) * ∑ s : Fin S, M.f x (M.zhat s) ≤
          (1 / (S : ℝ)) * ∑ s : Fin S, M.f x' (M.zhat s)) ∧
      IsDROOptimal M 0 τ₀ k x ∧
      ∀ (τ' k' : ℝ) (x' : E), IsDROOptimal M 0 τ' k' x' →
        τ' = τ₀ ∧ x' ∈ M.X ∧ ∀ x'' ∈ M.X,
          (1 / (S : ℝ)) * ∑ s : Fin S, M.f x' (M.zhat s) ≤
            (1 / (S : ℝ)) * ∑ s : Fin S, M.f x'' (M.zhat s) := by sorry

end DRORSEquiv
