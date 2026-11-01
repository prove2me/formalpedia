-- Prove2me | Theorems.Thm_DRORSEquiv_boundary_tauBar
-- name    : DRORSEquiv.boundary_tauBar
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:14.025345+00:00
-- url     : https://prove2.me/theorems/c9320b8a-0ba4-42f3-b7fa-d055b86336f0
-- title:
--   Proof of Theorem 1, p.33 — boundary case $\tau_{rs}=\bar\tau$: for $\theta\ge\bar\theta$, DRO($\theta$) and RS($\bar\tau$) have the same optimal decisions (corrected: $\bar\theta<\infty$)
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose $S\ge1$, the samples lie in $\mathcal Z$, $\rho(z,z)=0$, $\bar\tau=t$ is finite and $\bar\theta<\infty$. For every real $\theta\ge\bar\theta$ and every $x\in\mathcal X$ the following are equivalent:
--
--   1. $(\tau,k,x)$ is an optimal solution of DRO($\theta$) for some $\tau,k$;
--   2. $\displaystyle\sup_{z\in\mathcal Z}f(x,z)\le t$;
--   3. $(x,0)$ is an optimal solution of RS($t$).
--
--   This is the right boundary of Theorem 1: with the radius $\bar\theta$ the Wasserstein ball imposes no distance restriction, DRO becomes $\min_{x}\sup_z f(x,z)$, and RS($\bar\tau$) becomes the feasibility problem $\sup_z f(x,z)\le\bar\tau$.
--
--   Differences from the source:
--   - correction: θ = θ̄ = (1/S) Σ_s sup_z ρ(z, ẑ_s), possibly +∞ → θ̄ < ∞ assumed; reason: with θ̄ = ∞ no real radius works: f(x, z) = 1 − 1/(1+z), Z = [0, ∞), ρ = |·|, S = 1, ẑ₁ = 0, X = ℝ give τ̄ = 1 and RS(1) optimum (x, 0), while every DRO(θ) has value ≤ (1 − √ε)² + εθ < 1
--   - generalization: radius θ = θ̄ → every real radius θ ≥ θ̄; reason: the proof of Proposition 2, p.34, states it for θ ≥ θ̄; θ = θ̄ (real since θ̄ < ∞) is a special case
--   - correction: k*(τ̄) = 0 since all constraints could hold when k = 0 → (x, 0) is RS(τ̄)-optimal exactly when sup_z f(x, z) ≤ τ̄ (clause 3); κ(τ̄) = 0 is not asserted; reason: κ(τ̄) can be ∞ when τ̄ is not attained: X = [1, ∞), f(x, z) = 1/x, Z = [0, 1], ρ = |·|, ẑ₁ = 0 give τ̄ = 0 and h(x, k) = 1/x > 0
--   - reading: both problems have the same optimal solutions → the equivalence (1) ⇔ (2) ⇔ (3) for each decision x ∈ X; reason: the optimal solutions are compared through their decision x, as the page's displays do
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - reading: samples ẑ_s of the support (implicit), S the number of samples → hypotheses ∀ s, ẑ_s ∈ Z (and 0 < S where used); reason: implicit in the paper: the empirical distribution P† is the centre of the Wasserstein ball and lies in P(Z); every instance of the paper satisfies it
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33 (case τrs = τ̄); proof of Proposition 2, p.34

import Mathlib
import Definitions.Def_DRORSEquiv_IsRSOptimal
import Definitions.Def_DRORSEquiv_IsDROOptimal
import Definitions.Def_DRORSEquiv_tauBar
import Definitions.Def_DRORSEquiv_thetaBar

namespace DRORSEquiv

/-- **Boundary case `τrs = τ̄`** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33: "Simply let
θ̄ = 1/S ∑_{s∈[S]} sup_{z∈Z}{ρ(z, ẑs)} […], then the problem DRO(θ̄) becomes min_{x∈X} sup_{z∈Z} f(x,z) and
the problem RS(τ̄) becomes min_{x∈X} 0 s.t. sup_{z∈Z} f(x,z) ≤ τ̄. Since τ̄ = inf_{x∈X} sup_{z∈Z} f(x,z),
both problems have the same optimal solutions.").

Suppose `τ̄ = t` is finite and `θ̄ < ∞`. For every real `θ ≥ θ̄` and every `x ∈ X` the following are
equivalent: (i) `(τ, k, x)` is optimal for DRO(θ) for some `τ, k`; (ii) `sup_{z ∈ Z} f(x, z) ≤ t`;
(iii) `(x, 0)` is optimal for RS(t).

**Formalization Note.** Corrected: `θ̄ < ∞` is assumed (the page takes `θ = θ̄`, which is `+∞` on an
unbounded support, and then no real radius works: `f = 1 − 1/(1+z)` on `Z = [0, ∞)`). Generalization:
every `θ ≥ θ̄`, as in the proof of Proposition 2, p.34 ("For any θ ≥ θ̄, the problem DRO(θ) is always
equivalent to min_{x∈X} sup_{z∈Z} f(x,z)"). The page's "k∗(τrs) = 0" holds when `τ̄` is attained, which
is (iii). -/
theorem boundary_tauBar {E Ω : Type*} {S : ℕ} (M : Model E Ω S)
    (hS : 0 < S) (hzhat : ∀ s, M.zhat s ∈ M.Z) (hρ0 : ∀ z, M.ρ z z = 0)
    (t : ℝ) (ht : tauBar M = (t : EReal)) (hθbar : thetaBar M < ⊤)
    (θ : ℝ) (hθ : thetaBar M ≤ (θ : EReal)) (x : E) (hx : x ∈ M.X) :
    ((∃ τ k : ℝ, IsDROOptimal M θ τ k x) ↔ (⨆ z ∈ M.Z, (M.f x z : EReal)) ≤ (t : EReal)) ∧
      ((⨆ z ∈ M.Z, (M.f x z : EReal)) ≤ (t : EReal) ↔ IsRSOptimal M t x 0) := by sorry

end DRORSEquiv
