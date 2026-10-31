-- Prove2me | Theorems.Thm_DeltaSLearning_theorem_5
-- name    : DeltaSLearning.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:05:46.053994+00:00
-- url     : https://prove2.me/theorems/32b533c8-f8b1-46fe-a1d1-457bb0e3c74c
-- title:
--   Theorem 5 — high-probability regret bound for sub-exponential SGD (corrected: hypotheses for $i=1,\dots,n$, factor $\max(1,\beta)$ on the $b$ term)
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^d$ be nonempty, closed and convex with $\sup_{z_1,z_2\in\mathcal K}\|z_1-z_2\|\le\beta$, let $f$ be convex on $\mathcal K$, and let $(\mathcal F_i)$ be a filtration. Let $z_1\in\mathcal K$ be $\mathcal F_0$-measurable, let each $\tilde\nabla_i$ be $\mathcal F_i$-measurable, and
--   $$z_{i+1}=\mathrm{Proj}_{\mathcal K}\bigl[z_i-\eta_i\tilde\nabla_i\bigr],\qquad \eta_i=\frac{\beta}{\xi\sqrt i},\qquad i=1,\dots,n-1 .$$
--   Assume that for $i=1,\dots,n$, conditionally on $\mathcal F_{i-1}$:
--
--   1. $\tilde\nabla_i$ is a stochastic (sub)gradient of $f$ at $z_i$: $\mathbb E[\tilde\nabla_i\mid\mathcal F_{i-1}]$ is a subgradient of $f$ on $\mathcal K$ at $z_i$;
--   2. $\tilde\nabla_i$ is a $(\nu,b)$-sub-exponential random vector: for every unit vector $u$ and $|\lambda|<1/b$, $\mathbb E\bigl[e^{\lambda\langle u,\tilde\nabla_i-\mathbb E[\tilde\nabla_i\mid\mathcal F_{i-1}]\rangle}\mid\mathcal F_{i-1}\bigr]\le e^{\nu^2\lambda^2/2}$;
--   3. $\mathbb E[\|\tilde\nabla_i\|^2\mid\mathcal F_{i-1}]\le\xi^2$, with $\xi>0$.
--
--   Then for every minimizer $z^*$ of $f$ on $\mathcal K$ and every $\kappa\in(0,1)$, with probability at least $1-\kappa$,
--   $$\frac1n\sum_{i=1}^n\bigl[f(z_i)-f(z^*)\bigr]\le\max\Bigl\{\sqrt{\frac{2\beta^2\nu^2\log(1/\kappa)}{n}},\ \frac{2\max(1,\beta)\,b\log(1/\kappa)}{n}\Bigr\}+\frac{3\beta\xi}{2\sqrt n}.$$
--
--   The paper presents this bound as of independent interest; in the mission it controls the SGD part of the estimation error of Lemma 4.
--
--   Differences from the source:
--   - correction: hypothesis (b) for i = 1, …, n − 1 → hypotheses for i = 1, …, n; reason: the printed theorem is false: d = 1, K = [0, 1], β = 1, ξ = ν = b = 1, n = 2, z₁ = 0, f(z) = 10z², ∇̃₁ = ±1 with probability 1/2 (mean 0 = f′(0), second moment 1, sub-Gaussian so (1,1)-sub-exponential); η₁ = 1 gives z₂ = 1 with probability 1/2, and then (1/2)[f(z₁) + f(z₂)] − f(0) = 5 exceeds the bound max{1.18, 1.39} + 1.06 = 2.45 at κ = 1/4. The proof's (54) uses ∇̃_i for i = 1, …, n, and the hypothesis at i = n excludes the example
--   - correction: 2b log(1/δ)/n in the bound → 2 max(1, β) b log(1/κ)/n; reason: the printed term is false for large β, even with the hypotheses at i = 1, …, n: d = 1, K = [0, 10], β = 10, f(z) = 10z, z* = 0, z₁ = 10, n = 16, b = 1, ν = 0.1, the ∇̃_i i.i.d. with ∇̃_i = 0 with probability q = e⁻²⁰ and 10/(1 − q) otherwise (mean 10 = f′, second moment ξ² = 100/(1 − q), and the centered variable has E[e^{λ(·)}] ≤ e^{ν²λ²/2} for |λ| < 1). With probability q¹⁵ = e⁻³⁰⁰ every step leaves z_i = 10, so the average gap is 100; at κ = e⁻³⁰¹ the printed bound is max{6.13, 37.6} + 37.5 = 75.1. Step II of the proof calls ⟨∇f(z_i) − ∇̃_i, z_i − z*⟩ (βν, b)-sub-exponential, where Definition 6 gives (βν, βb). The factor max(1, β) leaves the printed term unchanged for β ≤ 1
--   - reading: conditional on z_i → conditional on F_{i−1}, for a filtration with z₁ F₀-measurable and ∇̃_i F_i-measurable; reason: the proof sets F_i = σ(∇̃₁, …, ∇̃_i) and equates E[· | F_{i−1}] with E[· | z_i] (p.40)
--   - generalization: ∇̃_i is a stochastic gradient of f at z_i: E[∇̃_i | z_i] = ∇f(z_i) → E[∇̃_i | F_{i−1}] is a subgradient of f on K at z_i; reason: the gradient of a differentiable convex f is such a subgradient, so this specializes to the source
--   - reading: the domain K of projected SGD, Proj_K → K nonempty, closed, convex; z_{i+1} a nearest point of K to z_i − η_i ∇̃_i; reason: Proj_K must be defined; for closed convex K the nearest point exists and is unique
--   - encoding: (ν, b)-sub-exponential random vector (Definition 6), conditional on the past → for all unit u and |λ| < 1/b (b = 0 read as 1/b = ∞): integrable exponential and conditional exponential moment ≤ e^{ν²λ²/2} a.s.; reason: Definition 6 applied conditionally; integrability is what the expectation presupposes
--   - encoding: the stochastic gradient has a second moment → ∇̃_i and ‖∇̃_i‖² integrable for i = 1, …, n; reason: what E[∇̃_i | F_{i−1}] and the second moment presuppose
--   - encoding: z* = argmin_{z ∈ K} f(z) → every minimizer z* ∈ K; reason: the argmin need not be unique; the bound is stated for each
--   - encoding: with probability at least 1 − δ, δ ∈ (0,1) implicit → κ ∈ (0, 1), P{bound} ≥ 1 − κ; reason: renamed to avoid the inventory gap δ; log(1/δ) needs δ < 1
--   - encoding: ℝ^d → EuclideanSpace ℝ (Fin d); reason: Lean's ℝ^d with the Euclidean norm
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 5, p.23; Definition 6, p.43; proof pp.39–40

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace DeltaSLearning

/-- **Theorem 5** (high-probability regret bound for sub-exponential SGD), corrected: the
hypotheses run over `i = 1, …, n`, and the term `2b log(1/κ)/n` carries a factor `max(1, β)`.
Let `K ⊆ ℝ^d` be nonempty, closed and convex with diameter at most `β`, `f` convex on `K`
with a minimizer `z* ∈ K`, and `z_1 ∈ K`, `z_{i+1} = Proj_K[z_i - η_i ∇̃_i]` with
`η_i = β/(ξ√i)`, for `i = 1, …, n - 1`. Suppose that for `i = 1, …, n`, given the past
`F_{i-1}`, `∇̃_i` is a stochastic (sub)gradient of `f` at `z_i`, is a `(ν, b)`-sub-exponential
random vector (Definition 6) and has second moment at most `ξ²`. Then for every `κ ∈ (0, 1)`,
with probability at least `1 - κ`,
`(1/n) Σ_{i=1}^n [f(z_i) - f(z*)] ≤ max{√(2β²ν² log(1/κ)/n), 2 max(1, β) b log(1/κ)/n} + 3βξ/(2√n)`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Theorem 5, p.23; Definition 6, p.43; proof pp.39–40.

**Formalization Note** (a) The page states hypothesis (b) for `i = 1, …, n - 1`; the conclusion
is false with that range (counterexample in the item's description), and the proof (54) uses
`∇̃_i` for `i = 1, …, n`, so the hypotheses are stated for `i = 1, …, n`. (b) "Conditional on
`z_i`" is read as conditional on `F_{i-1}` for a filtration to which `z_1` (at `F_0`) and each
`∇̃_i` (at `F_i`) are adapted, as the proof does (p.40). (c) Unbiasedness is stated as: the
conditional mean `E[∇̃_i | F_{i-1}]` is a subgradient of `f` on `K` at `z_i`; for a
differentiable `f` this is the paper's `E[∇̃_i | z_i] = ∇f(z_i)`. (d) `Proj_K` is the nearest
point of `K`. (e) The paper's confidence `δ` is renamed `κ`. (f) `b = 0` reads `1/b = ∞`.
(g) The page's term `2b log(1/δ)/n` is false for large `β` (counterexample in the item's
description): the proof's Step II calls `⟨∇f(z_i) - ∇̃_i, z_i - z*⟩` `(βν, b)`-sub-exponential,
where Definition 6 gives `(βν, βb)`. The term is stated with `max(1, β) b`, which is the page's
term for `β ≤ 1`. -/
theorem theorem_5 {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ m0) (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (hKne : K.Nonempty) (β ν b ξ : ℝ) (hβ : 0 ≤ β) (hν : 0 ≤ ν)
    (hb : 0 ≤ b) (hξ : 0 < ξ) (hdiam : ∀ z₁ ∈ K, ∀ z₂ ∈ K, ‖z₁ - z₂‖ ≤ β)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ K f) (n : ℕ) (hn : 1 ≤ n)
    (z g : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hz₁ : ∀ ω, z 1 ω ∈ K) (hz₁m : StronglyMeasurable[ℱ 0] (z 1))
    (hgm : ∀ i, StronglyMeasurable[ℱ i] (g i))
    (hstep : ∀ i, 1 ≤ i → i < n → ∀ ω, z (i + 1) ω ∈ K ∧
      ∀ w ∈ K, ‖z i ω - (β / (ξ * Real.sqrt i)) • g i ω - z (i + 1) ω‖ ≤
        ‖z i ω - (β / (ξ * Real.sqrt i)) • g i ω - w‖)
    (hint : ∀ i, 1 ≤ i → i ≤ n → Integrable (g i) P ∧ Integrable (fun ω => ‖g i ω‖ ^ 2) P)
    (hunb : ∀ i, 1 ≤ i → i ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ K,
      f (z i ω) + ⟪(P[g i | ℱ (i - 1)]) ω, w - z i ω⟫ ≤ f w)
    (hsub : ∀ i, 1 ≤ i → i ≤ n → ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
      ∀ l : ℝ, (b = 0 ∨ |l| < 1 / b) →
        Integrable (fun ω => Real.exp (l * ⟪u, g i ω - (P[g i | ℱ (i - 1)]) ω⟫)) P ∧
        ∀ᵐ ω ∂P, (P[fun ω' => Real.exp (l * ⟪u, g i ω' - (P[g i | ℱ (i - 1)]) ω'⟫) | ℱ (i - 1)]) ω
          ≤ Real.exp (ν ^ 2 * l ^ 2 / 2))
    (hmom : ∀ i, 1 ≤ i → i ≤ n → ∀ᵐ ω ∂P, (P[fun ω' => ‖g i ω'‖ ^ 2 | ℱ (i - 1)]) ω ≤ ξ ^ 2)
    (zstar : EuclideanSpace ℝ (Fin d)) (hzstar : zstar ∈ K) (hmin : ∀ w ∈ K, f zstar ≤ f w)
    (κ : ℝ) (hκ₀ : 0 < κ) (hκ₁ : κ < 1) :
    ENNReal.ofReal (1 - κ) ≤
      P {ω | (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, (f (z i ω) - f zstar) ≤
        max (Real.sqrt (2 * β ^ 2 * ν ^ 2 * Real.log (1 / κ) / n)) (2 * max 1 β * b * Real.log (1 / κ) / n)
          + 3 * β * ξ / (2 * Real.sqrt n)} := by sorry

end DeltaSLearning
