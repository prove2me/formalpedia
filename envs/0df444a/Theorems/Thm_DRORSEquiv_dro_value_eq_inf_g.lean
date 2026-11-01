-- Prove2me | Theorems.Thm_DRORSEquiv_dro_value_eq_inf_g
-- name    : DRORSEquiv.dro_value_eq_inf_g
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:31.944714+00:00
-- url     : https://prove2.me/theorems/7d03bf97-fb07-474b-9065-8f9aa96e2c4b
-- title:
--   Proof of Theorem 1, p.33 — Problem (DRO) rewritten as $\min_{\tau\ge Z_0}\tau+\kappa(\tau)\theta$
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose the samples lie in $\mathcal Z$ and $\rho(z,z)=0$. For every radius $\theta\ge0$, with $g(\tau,\theta)=\tau+\kappa(\tau)\theta$,
--
--   $$\inf\big\{\tau+k\theta:\ x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\big\}=\inf\big\{g(\tau,\theta):\ \tau\ge Z_0,\ \kappa(\tau)<\infty\big\}.$$
--
--   That is, the optimal value of DRO($\theta$) is obtained by first solving RS($\tau$) for each target and then optimizing over the target; this reduces Theorem 1 to a one-dimensional problem in $\tau$.
--
--   Differences from the source:
--   - reading: min_{τ≥Z0} g(τ, θ) with g(τ, θ) = τ + k*(τ)θ → infimum over τ ≥ Z0 with κ(τ) < ∞, as an equality of optimal values; reason: k*(τ) is "the optimal value of RS(τ)", defined where RS(τ) is feasible; at θ = 0 an infeasible τ would otherwise contribute τ + 0·∞
--   - encoding: min over (τ, k, x) and over τ → infima in EReal; reason: Lean convention; attainment is not part of the rewriting
--   - reading: θ the DRO radius → θ ≥ 0; reason: the Wasserstein radius is nonnegative
--   - reading: samples ẑ_s of the support (implicit), S the number of samples → hypotheses ∀ s, ẑ_s ∈ Z (and 0 < S where used); reason: implicit in the paper: the empirical distribution P† is the centre of the Wasserstein ball and lies in P(Z); every instance of the paper satisfies it
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.33

import Mathlib
import Definitions.Def_DRORSEquiv_IsFeasible
import Definitions.Def_DRORSEquiv_rsValue
import Definitions.Def_DRORSEquiv_empiricalOptimum

open scoped ENNReal

namespace DRORSEquiv

/-- **Problem (DRO) rewritten through the RS value function** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A, proof of
Theorem 1, p.33: "We first define k∗(τ) as the optimal value of the problem RS(τ) and
g(τ,θ) = τ + k∗(τ)θ. Then we can rewrite the problem (DRO) as: min_{τ≥Z0} g(τ,θ).").

For every real `θ ≥ 0`, the optimal value of DRO(θ), `inf { τ + kθ : x ∈ X, k ≥ 0, h(x, k) ≤ τ }`,
equals `inf { τ + θ κ(τ) : τ ≥ Z₀, κ(τ) < ∞ }`.

**Formalization Note.** Both infima are taken in `EReal`. Reading: `g(τ, θ)` is used only where RS(τ) is
feasible, since `k∗(τ)` is "the optimal value of RS(τ)"; at `θ = 0` an infeasible `τ` would otherwise
contribute `τ + 0 · ∞`. The samples lie in `Z` and `ρ(z, z) = 0`, which give `τ ≥ Z₀` on the feasible
set. -/
theorem dro_value_eq_inf_g {E Ω : Type*} {S : ℕ} (M : Model E Ω S)
    (hzhat : ∀ s, M.zhat s ∈ M.Z) (hρ0 : ∀ z, M.ρ z z = 0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (⨅ (τ : ℝ) (k : ℝ) (x : E) (_ : IsFeasible M τ x k), ((τ + k * θ : ℝ) : EReal)) =
      ⨅ (τ : ℝ) (_ : empiricalOptimum M ≤ (τ : EReal) ∧ rsValue M τ < ⊤),
        ((τ + θ * (rsValue M τ).toReal : ℝ) : EReal) := by sorry

end DRORSEquiv
