-- Prove2me | Theorems.Thm_DRORSEquiv_subdiff_nonempty_bounded
-- name    : DRORSEquiv.subdiff_nonempty_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:14.611006+00:00
-- url     : https://prove2.me/theorems/83cb09e2-4469-4784-8538-940fc7e2d66a
-- title:
--   Proof of Theorem 1, p.34 — $\partial\kappa(\tau_{rs})$ is nonempty and bounded for $\tau_{rs}\in\operatorname{int}(\operatorname{dom}\kappa)$
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose $\mathcal X$ is convex and $f(\cdot,z)$ is convex on $\mathcal X$ for every $z\in\mathcal Z$. If $\tau_{rs}$ is an interior point of $\operatorname{dom}\kappa=\{\tau:\kappa(\tau)<\infty\}$, then the subdifferential $\partial\kappa(\tau_{rs})$ is nonempty and bounded.
--
--   This supplies the subgradient $\alpha\in\partial\kappa(\tau_{rs})$ from which Theorem 1 builds the radius $\theta^*=-1/\alpha$.
--
--   Differences from the source:
--   - generalization: the setting of Theorem 1 (x ∈ ℝⁿ, f convex in x, Polish (Z, ρ), f ∈ L¹, bounded growth) → f(·, z) convex on X, X in any real vector space, any ρ, no measure-level assumptions; reason: the paper's instances satisfy these weaker hypotheses
--   - encoding: ∂k*(τrs) bounded → Bornology.IsBounded (subdiff κ τrs) with the convex-analysis subdifferential (empty where κ = ∞); reason: standard convention; same set at points of dom κ
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Appendix A, proof of Theorem 1, p.34

import Mathlib
import Definitions.Def_DRORSEquiv_rsValue
import Definitions.Def_DRORSEquiv_subdiff

namespace DRORSEquiv

/-- **Nonempty bounded subdifferential in the interior of the domain** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Appendix A,
proof of Theorem 1, p.34: "In addition, τrs ∈ int(dom k∗), so we have that ∂k∗(τrs) is nonempty and
bounded.").

If `X` is convex, `f(·, z)` is convex on `X` for every `z ∈ Z`, and `τrs` is an interior point of
`dom κ = {τ : κ(τ) < ∞}`, then `∂κ(τrs)` is nonempty and bounded.

**Formalization Note.** The preceding claim of the page ("k∗(τrs) is finite […] whenever τrs ≥ Z0") is
false (`f(x, z) = 1_{z ≠ 0}`, `Z = [−1, 1]`, `ẑ₁ = 0`: RS(1/2) is infeasible) and is not stated; the
interior hypothesis is the page's own. The convexity hypotheses are those of Theorem 1 (they make `κ`
convex, Lemma 1). -/
theorem subdiff_nonempty_bounded {E Ω : Type*} [AddCommGroup E] [Module ℝ E] {S : ℕ}
    (M : Model E Ω S)
    (hX : Convex ℝ M.X) (hf : ∀ z ∈ M.Z, ConvexOn ℝ M.X (fun x => M.f x z))
    (τrs : ℝ) (hint : τrs ∈ interior {τ : ℝ | rsValue M τ < ⊤}) :
    (subdiff (rsValue M) τrs).Nonempty ∧ Bornology.IsBounded (subdiff (rsValue M) τrs) := by sorry

end DRORSEquiv
