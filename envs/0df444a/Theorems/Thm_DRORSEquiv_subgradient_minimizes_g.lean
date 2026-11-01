-- Prove2me | Theorems.Thm_DRORSEquiv_subgradient_minimizes_g
-- name    : DRORSEquiv.subgradient_minimizes_g
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:37:57.292152+00:00
-- url     : https://prove2.me/theorems/22418317-0eaa-4193-af73-af8d357513ba
-- title:
--   Proof of Theorem 1, p.34 — for $\alpha\in\partial\kappa(\tau_{rs})$, $\alpha<0$, the radius $\theta^*=-1/\alpha$ makes $\tau_{rs}$ minimize $\tau+\kappa(\tau)\theta^*$
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Let $\alpha\in\partial\kappa(\tau_{rs})$ with $\alpha<0$ and put $\theta^*=-1/\alpha>0$. Then $g(\tau,\theta^*)=\tau+\kappa(\tau)\theta^*$ attains its minimum over $\tau\in\mathbb R$ at $\tau=\tau_{rs}$:
--
--   $$\tau_{rs}+\theta^*\kappa(\tau_{rs})\le\tau+\theta^*\kappa(\tau)\qquad\text{for all }\tau\in\mathbb R .$$
--
--   Combined with the rewriting of Problem (DRO) as $\min_\tau g(\tau,\theta)$, this shows that DRO($\theta^*$) and RS($\tau_{rs}$) share their optimal solutions.
--
--   **Formalization Note** Both sides are evaluated in `EReal`, with $\theta^*\cdot\infty=\infty$.
--
--   Differences from the source:
--   - generalization: τrs ∈ int(dom k*), k* convex (the setting of Theorem 1), Moreau–Rockafellar: 0 = 1 + θ*α ∈ ∂τ g(τrs, θ*) → any α ∈ ∂κ(τrs) with α < 0, no interior or convexity hypothesis; reason: the minimizing property follows from the subgradient inequality alone; the page's setting is a special case
--   - generalization: min_{τ ≥ Z0} g(τ, θ*) → minimum over all τ ∈ ℝ; reason: for τ < Z0 κ(τ) = ∞ when the samples lie in Z, so the page's minimum is the same; in general the claim over all τ implies it
--   - encoding: g(τ, θ*) = τ + k*(τ)θ*, real → computed in EReal with κ ∈ [0, ∞]; reason: Lean convention; agrees where κ is finite
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.34

import Mathlib
import Definitions.Def_DRORSEquiv_rsValue
import Definitions.Def_DRORSEquiv_subdiff

namespace DRORSEquiv

/-- **A negative subgradient gives the DRO radius** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of Theorem 1,
p.34: "Therefore 0 = 1 + θ∗α ∈ 1 + θ∗∂k∗(τrs) = ∂τ g(τrs, θ∗), where g(τ, θ∗) = τ + k∗(τ)θ∗. Thus, we find
the θ∗ to make min_{τ≥Z0} g(τ, θ∗) reach the minimum at τ = τrs.").

If `α ∈ ∂κ(τrs)` and `α < 0`, then with `θ* = −1/α` the function `g(τ, θ*) = τ + θ* κ(τ)` attains its
minimum over `τ ∈ ℝ` at `τ = τrs`.

**Formalization Note.** `g` is evaluated in `EReal` (`θ* · ∞ = ∞` for `θ* > 0`). Generalization: the page
derives `0 ∈ ∂_τ g(τrs, θ*)` by the Moreau–Rockafellar theorem using `τrs ∈ int(dom κ)` and convexity of `κ`;
the conclusion holds for every subgradient without those hypotheses, and the minimum is over all real `τ`
(below `Z₀` `κ = ∞`). -/
theorem subgradient_minimizes_g {E Ω : Type*} {S : ℕ} (M : Model E Ω S)
    (τrs α : ℝ) (hα : α ∈ subdiff (rsValue M) τrs) (hneg : α < 0) (τ : ℝ) :
    (τrs : EReal) + ((-1 / α : ℝ) : EReal) * (rsValue M τrs : EReal) ≤
      (τ : EReal) + ((-1 / α : ℝ) : EReal) * (rsValue M τ : EReal) := by sorry

end DRORSEquiv
