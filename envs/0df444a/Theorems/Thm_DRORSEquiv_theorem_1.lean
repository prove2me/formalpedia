-- Prove2me | Theorems.Thm_DRORSEquiv_theorem_1
-- name    : DRORSEquiv.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:09.606982+00:00
-- url     : https://prove2.me/theorems/ac8fbc56-bd9d-473e-baf6-ca20c1efc464
-- title:
--   Theorem 1, p.8 — RS($\tau_{rs}$) optima are DRO($\theta^*$) optima, $\theta^*=-1/\alpha$ (corrected: endpoint $\bar\tau$ needs $\bar\theta<\infty$ or $\kappa=\infty$ below it; $\alpha<0$)
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose $\mathcal X$ is convex, $f(\cdot,z)$ is convex on $\mathcal X$ for every $z\in\mathcal Z$, $\bar\tau=t$ is finite, and $Z_0\le\tau_{rs}\le t$.
--
--   1. **Existence.** If $\tau_{rs}<\bar\tau$, or $\tau_{rs}=\bar\tau$ and either $\bar\theta<\infty$ or $\kappa(\tau)=\infty$ for every $\tau<\tau_{rs}$ ($\tau_{rs}$ is the left end of the domain of $\kappa$, e.g. $\tau_{rs}=Z_0$), there is a radius $\theta^*\ge0$ such that for **every** optimal solution $(x^*,k^*)$ of RS($\tau_{rs}$), the triple $(\tau_{rs},k^*,x^*)$ is an optimal solution of DRO($\theta^*$).
--   2. **Explicit radius.** For every optimal solution $(x^*,k^*)$ of RS($\tau_{rs}$) and every subgradient $\alpha\in\partial\kappa(\tau_{rs})$:
--      - if $\tau_{rs}<\bar\tau$ then $\alpha<0$;
--      - if $\alpha<0$ then $(\tau_{rs},k^*,x^*)$ is an optimal solution of DRO($\theta^*$) with
--
--   $$\theta^*=-\frac1{\alpha}.$$
--
--   Together with the easy converse (Proposition 1), the theorem says that as their parameters vary the Wasserstein DRO model and the robust satisficing model trace the same family of optimal solutions, and it gives the parameter map $\tau\mapsto\theta^*=-1/\alpha(\tau)$ explicitly.
--
--   Differences from the source:
--   - correction: existence of θ* for every τrs ∈ [Z0, τ̄] → for τrs < τ̄, and at τrs = τ̄ when θ̄ < ∞ or κ = ∞ on (−∞, τrs) (then θ* = 0, as in the page's case τrs = Z0); reason: at τ̄ the statement fails when θ̄ = ∞ and τ̄ is not the left end of dom κ: f(x, z) = 1 − 1/(1+z), Z = [0, ∞), ρ = |·|, S = 1, ẑ₁ = 0, X = ℝ (convex, f bounded, growth rate 0) give Z0 = 0, τ̄ = 1, RS(1) optimum (x, 0), and every DRO(θ) has value ≤ (1 − √ε)² + εθ < 1, so (1, 0, x) is never DRO-optimal
--   - correction: θ* = −1/α(τ) with α(τ) ∈ ∂κ(τ) any subgradient, for any τ ∈ [Z0, τ̄] → α < 0 for every subgradient when τrs < τ̄, and θ* = −1/α for every subgradient α < 0 (any τrs ∈ [Z0, τ̄]), with no claim that ∂κ(τrs) is nonempty; reason: at τ̄ a subgradient can be 0: f(x, z) = z, Z = [0, 1], ρ = |·|, S = 1, ẑ₁ = 0 give κ(τ) = (1 − τ)⁺ on [0, ∞), τ̄ = 1, ∂κ(1) = [−1, 0] ∋ 0, and −1/0 is undefined; and ∂κ(τrs) can be empty: X = {0}, f(x, 0) = 0, f(x, z) = 1 + z − z² on (0, 1], Z = [0, 1], ρ = |·|, S = 1, ẑ₁ = 0 give Z0 = 0, τ̄ = 5/4, κ = ∞ on (−∞, 1), κ(τ) = 1 − 2√(τ − 1) on [1, 5/4], so RS(1) has the optimum (0, 1) and ∂κ(1) = ∅ (there θ* = 0 from the existence clause)
--   - reading: the optimal solution to Problem (RS) is also optimal to Problem (DRO) → every optimal solution (x*, k*) of RS(τrs), with one θ* for all of them, gives the DRO solution (τ, k, x) = (τrs, k*, x*); reason: the proof shows that τrs minimizes τ + θ*κ(τ), which transfers every RS optimum; the stronger reading; the DRO triple is the one of the proof ("reach the minimum at τ = τrs")
--   - reading: Problem (RS) with parameter τ → parameter τrs; reason: the statement fixes τrs; τ is a slip
--   - generalization: x ∈ ℝⁿ, Z ⊆ ℝᵐ with (Z, ρ) Polish, f(x, ·) ∈ L¹(P†), bounded growth rate, f convex in x → X in any real vector space, Z any set, ρ any cost with ρ ≥ 0 and ρ(z, z) = 0, no measure-level assumptions, f(·, z) convex on X; reason: the standing assumptions of p.7 serve only the reformulations (1) ⇔ (DRO) and (2) ⇔ (RS); every instance of the paper is an instance
--   - encoding: subgradient inequality κ(τ) ≥ κ(τrs) + α(τ − τrs) for τ ≥ Z0 → for all τ ∈ ℝ, ∂κ(τrs) = ∅ where κ(τrs) = ∞; reason: κ = ∞ below Z0 when the samples lie in Z, so the sets agree
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - reading: samples ẑ_s of the support (implicit), S the number of samples → hypotheses ∀ s, ẑ_s ∈ Z (and 0 < S where used); reason: implicit in the paper: the empirical distribution P† is the centre of the Wasserstein ball and lies in P(Z); every instance of the paper satisfies it
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Theorem 1, p.8; proof in Appendix A, pp.33–34

import Mathlib
import Definitions.Def_DRORSEquiv_IsRSOptimal
import Definitions.Def_DRORSEquiv_IsDROOptimal
import Definitions.Def_DRORSEquiv_rsValue
import Definitions.Def_DRORSEquiv_subdiff
import Definitions.Def_DRORSEquiv_empiricalOptimum
import Definitions.Def_DRORSEquiv_tauBar
import Definitions.Def_DRORSEquiv_thetaBar

namespace DRORSEquiv

/-- **Theorem 1: robust satisficing optima are Wasserstein-DRO optima** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Theorem 1,
p.8: "Suppose the feasible set X is convex and f(x,z) is convex in x for every z ∈ Z. For a fixed
τrs ∈ [Z0, τ̄], there exists a θ∗, such that the optimal solution to Problem (RS) with parameter τ is also
optimal to Problem (DRO) with parameter θ∗. In addition, the corresponding θ∗ can be obtained explicitly
via θ∗ = −1/α(τ), where α(τ) ∈ ∂κ(τ) is a subgradient for any τ ∈ [Z0, τ̄].").

Let `X` be convex, `f(·, z)` convex on `X` for every `z ∈ Z`, `τ̄ = t` finite and `Z₀ ≤ τrs ≤ t`.
(a) If `τrs < t`, or `τrs = t` and either `θ̄ < ∞` or `κ = ∞` on `(−∞, τrs)` (`τrs` is the left end of
`dom κ`, e.g. `τrs = Z₀`), there is one `θ* ≥ 0` such that for every optimal solution
`(x*, k*)` of RS(τrs), `(τrs, k*, x*)` is optimal for DRO(θ*).
(b) For every optimal solution `(x*, k*)` of RS(τrs) and every `α ∈ ∂κ(τrs)`: if `τrs < t` then `α < 0`;
and if `α < 0` then `(τrs, k*, x*)` is optimal for DRO(−1/α).

**Formalization Note.** Corrections: at `τrs = τ̄` the existence needs `θ̄ < ∞` or `τrs` the left end of
`dom κ` (where `θ* = 0` works, as in the page's case `τrs = Z₀`) (counterexample
`f(x, z) = 1 − 1/(1+z)`, `Z = [0, ∞)`, `ρ = |·|`, `ẑ₁ = 0`: no real radius makes the RS(1) optimum
DRO-optimal); the formula `θ* = −1/α` needs `α < 0` (`f = z` on `[0, 1]`, `ẑ₁ = 0`: `0 ∈ ∂κ(1)`), and `∂κ(τrs)` is not claimed nonempty
(at the left end of `dom κ` it can be empty; there (a) gives `θ* = 0`).
"The optimal solution" is read as every optimal solution, with one `θ*`; the RS solution `(x*, k*)`
becomes the DRO solution `(τ, k, x) = (τrs, k*, x*)`. The statement's "parameter τ" is `τrs`. `κ`, `Z₀`,
`τ̄`, `θ̄` are infima/suprema in `[0, ∞]` or `EReal`. The paper's standing assumptions of p.7 (Polish
support, integrability, bounded growth rate) are not needed; `ρ` is any cost with `ρ ≥ 0`, `ρ(z, z) = 0`;
`E` is any real vector space; the samples lie in `Z`. -/
theorem theorem_1 {E Ω : Type*} [AddCommGroup E] [Module ℝ E] {S : ℕ} (M : Model E Ω S)
    (hX : Convex ℝ M.X) (hf : ∀ z ∈ M.Z, ConvexOn ℝ M.X (fun x => M.f x z))
    (hS : 0 < S) (hzhat : ∀ s, M.zhat s ∈ M.Z)
    (hρ : ∀ z w, 0 ≤ M.ρ z w) (hρ0 : ∀ z, M.ρ z z = 0)
    (t : ℝ) (ht : tauBar M = (t : EReal)) (τrs : ℝ)
    (hlo : empiricalOptimum M ≤ (τrs : EReal)) (hhi : τrs ≤ t) :
    ((τrs < t ∨ (τrs = t ∧ (thetaBar M < ⊤ ∨ ∀ τ : ℝ, τ < τrs → rsValue M τ = ⊤))) →
        ∃ θ : ℝ, 0 ≤ θ ∧ ∀ (x : E) (k : ℝ), IsRSOptimal M τrs x k → IsDROOptimal M θ τrs k x) ∧
      ∀ (x : E) (k : ℝ), IsRSOptimal M τrs x k → ∀ α ∈ subdiff (rsValue M) τrs,
        (τrs < t → α < 0) ∧ (α < 0 → IsDROOptimal M (-1 / α) τrs k x) := by sorry

end DRORSEquiv
