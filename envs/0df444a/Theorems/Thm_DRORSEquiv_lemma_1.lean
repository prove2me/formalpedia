-- Prove2me | Theorems.Thm_DRORSEquiv_lemma_1
-- name    : DRORSEquiv.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:38:11.19597+00:00
-- url     : https://prove2.me/theorems/23d055ce-5659-4d6e-aada-f6d56b5c9575
-- title:
--   Lemma 1, p.33 — the RS value function $\kappa$ is convex (corrected: $\mathcal X$ convex)
-- statement:
--   Throughout, $\mathcal X$ is a set of decisions in a real vector space, $\mathcal Z$ a support set of outcomes, $\rho(z,z')\ge0$ a transport cost with $\rho(z,z)=0$, $\hat z_1,\dots,\hat z_S\in\mathcal Z$ ($S\ge1$) the historical samples, and $f(x,z)$ a real cost. The worst-case loss is $h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\{f(x,z)-k\rho(z,\hat z_s)\}$; Problem (RS) with target $\tau$ minimizes $k$ over $\{x\in\mathcal X,\ k\ge0,\ h(x,k)\le\tau\}$ with value $\kappa(\tau)\in[0,\infty]$; Problem (DRO) with radius $\theta$ minimizes $\tau+k\theta$ over the triples $(\tau,k,x)$ with $x\in\mathcal X$, $k\ge0$, $h(x,k)\le\tau$. $Z_0=\inf_{x\in\mathcal X}\frac1S\sum_s f(x,\hat z_s)$ is the empirical optimum, $\bar\tau=\inf_{x\in\mathcal X}\sup_{z\in\mathcal Z}f(x,z)$ and $\bar\theta=\frac1S\sum_s\sup_{z\in\mathcal Z}\rho(z,\hat z_s)$.
--
--   Suppose $\mathcal X$ is convex and $f(\cdot,z)$ is convex on $\mathcal X$ for every $z\in\mathcal Z$. Then $\kappa$ is convex: for all real $\tau_1,\tau_2$ and $\lambda\in[0,1]$,
--
--   $$\kappa\big(\lambda\tau_1+(1-\lambda)\tau_2\big)\le\lambda\,\kappa(\tau_1)+(1-\lambda)\,\kappa(\tau_2)\qquad\text{in }[0,\infty].$$
--
--   Convexity of $\kappa$ is what gives subgradients of $\kappa$ in the interior of its domain, from which the radius $\theta^*=-1/\alpha$ of Theorem 1 is built.
--
--   **Formalization Note** The inequality is in $[0,\infty]$ with $0\cdot\infty=0$.
--
--   Differences from the source:
--   - correction: k*(τ) is convex if f(x, z) is convex over x → X convex is added; reason: the proof uses it ("due to the convexity of set X"); without it the lemma fails: X = {0, 1}, f(x, z) = (1 − x)z + x/2, Z = [0, 1], ρ = |·|, S = 1, ẑ₁ = 0 give κ(0) = 1, κ(1/4) = 3/4, κ(1/2) = 0
--   - generalization: τ1, τ2 ≥ Z0 → all real τ1, τ2; reason: restricting to τ1, τ2 ≥ Z0 gives the page's statement
--   - generalization: f(x, z) convex over x (x ∈ ℝⁿ), (Z, ρ) Polish metric, f ∈ L¹, bounded growth → f(·, z) convex on X for z ∈ Z, X in any real vector space, any ρ, no measure-level assumptions; reason: the paper's instances satisfy these weaker hypotheses
--   - encoding: convexity of the real function k* → convexity inequality for the [0, ∞]-valued κ with weights ofReal λ, ofReal (1 − λ); reason: κ is ∞ off its domain; on the domain this is ordinary convexity
--   - encoding: κ(τ) := min k, Z0 := min, τ̄ := inf … finite → κ is an infimum in [0, ∞] (∞ iff RS(τ) infeasible); Z0, τ̄, θ̄ are infima/suprema in EReal; τ̄ finite is τ̄ = t with t real; reason: Lean convention; where the paper's minimum exists the values agree, and optimal solutions are assumed explicitly where the paper's min presupposes them
--   - encoding: samples indexed by [S] = {1, …, S} → samples indexed by Fin S (0-based); reason: relabelling; same instances
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), Lemma 1, p.33

import Mathlib
import Definitions.Def_DRORSEquiv_rsValue

open scoped ENNReal

namespace DRORSEquiv

/-- **Lemma 1: the RS value function is convex** (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), Lemma 1, p.33: "k∗(τ) is convex if
the function f(x,z) is convex over x.").

If `X` is convex and `f(·, z)` is convex on `X` for every `z ∈ Z`, then for all real `τ₁, τ₂` and
`λ ∈ [0, 1]`, `κ(λτ₁ + (1−λ)τ₂) ≤ λ κ(τ₁) + (1−λ) κ(τ₂)` in `[0, ∞]`.

**Formalization Note.** Corrected: `X` convex is added; the proof uses it ("due to the convexity of set
X"), and without it the lemma fails (`X = {0, 1}`, `f(x, z) = (1 − x)z + x/2`, `Z = [0, 1]`, `ẑ₁ = 0`:
`κ(0) = 1`, `κ(1/4) = 3/4`, `κ(1/2) = 0`). Convexity is stated for the `[0, ∞]`-valued `κ` with real
weights (`0 · ∞ = 0`), over all real `τ₁, τ₂` (the page has `τ₁, τ₂ ≥ Z₀`; below `Z₀` `κ = ∞`). The page
assumes the minimizers exist; `κ` here is an infimum. -/
theorem lemma_1 {E Ω : Type*} [AddCommGroup E] [Module ℝ E] {S : ℕ} (M : Model E Ω S)
    (hX : Convex ℝ M.X) (hf : ∀ z ∈ M.Z, ConvexOn ℝ M.X (fun x => M.f x z))
    (τ₁ τ₂ l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    rsValue M (l * τ₁ + (1 - l) * τ₂) ≤
      ENNReal.ofReal l * rsValue M τ₁ + ENNReal.ofReal (1 - l) * rsValue M τ₂ := by sorry

end DRORSEquiv
