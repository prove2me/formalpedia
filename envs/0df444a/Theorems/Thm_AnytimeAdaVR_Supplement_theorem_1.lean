-- Prove2me | Theorems.Thm_AnytimeAdaVR_Supplement_theorem_1
-- name    : AnytimeAdaVR.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:30:50.480489+00:00
-- url     : https://prove2.me/theorems/45ca65c0-11f7-43fe-87a6-55a23b413b2e
-- title:
--   Theorem 1 — Algorithm 1 uses $7n-1\le T$ evaluations and attains $(\Delta_f+3L+7\sigma)n^{-1/4}$, $(\Delta_f+3L+3\bar L+12\sigma)n^{-1/3}$, $(\Delta_f+4L)n^{-1/2}$
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ and a stochastic gradient $g(x;\xi)$, with $\xi$ drawn from a probability measure $\mu$, satisfy Assumption 1 (differentiable $f$ with $L$-Lipschitz gradient, $L>0$, $f^*>-\infty$, $f(x_{\mathrm{init}})-f^*\le\Delta_f$, $\Delta_f\ge0$) and Assumption 2 (unbiased gradients with variance at most $\sigma^2$, $\sigma\ge0$). For any integer $T\ge7$ let $n=\lfloor T/7\rfloor$. Then Algorithm 1 uses exactly $7n-1\le T$ gradient evaluations and returns a point $\hat x_T$ such that
--   $$
--   \mathbb E\,\|\nabla f(\hat x_T)\|\le
--   \begin{cases}
--   (\Delta_f+3L+7\sigma)\,n^{-1/4}, & \text{under the two basic assumptions},\\
--   (\Delta_f+3L+3\bar L+12\sigma)\,n^{-1/3}, & \text{if also } \mathbb E\|g(x;\xi)-g(y;\xi)\|^2\le\bar L^2\|x-y\|^2 \text{ for all } x,y,\\
--   (\Delta_f+4L)\,n^{-1/2}, & \text{if } g(x;\xi)=\nabla f(x) \text{ almost surely}.
--   \end{cases}
--   $$
--   All three bounds hold for the same output of the same algorithm, which does not use $L$, $\bar L$, $\sigma$, $\Delta_f$, or the applicable oracle condition.
--
--   This is the paper's fixed-budget result: one parameter-free three-stage method matches the optimal rate exponents of the basic stochastic, the average-smooth and the noiseless regimes, and Theorem 2 removes the need to know the budget.
--
--   **Formalization Note** The evaluation count is the counter of the `StateM ℕ` computation `alg1Run`, which counts every gradient evaluation; the theorem states it equals $7n-1$ on every realization of the randomness. Expectations are lower integrals of $\|\cdot\|$ over the published tape law `tapeMeasure μ`. The average-smooth clause holds for every $\bar L$ satisfying Assumption 3.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined (the base mission's convention)
--   - encoding: fresh samples, independent reservoir coins and fresh validation samples → the published tape AnytimeAdaVR.Tape under tapeMeasure μ (stage i uses samples (i, t) and coins (i, r), validation of candidate i uses samples (i, 0, j)); reason: all used coordinates are independent with the oracle's law and uniform coins; same law of every quantity the algorithm uses
--   - encoding: "with probability 1/(t + 1), set X_i ← x_t" → replace iff the uniform coin U(t + 1) ≤ 1/(t + 1); reason: an event of probability 1/(t + 1) independent of the samples; same algorithm
--   - encoding: "Algorithm 1 uses 7n − 1 ≤ T gradient evaluations" → the evaluation counter of alg1Run equals 7·(T/7) − 1 on every tape, and 7·(T/7) − 1 ≤ T; reason: every gradient evaluation of the algorithm increments the counter, so the counter is the paper's count; natural-number subtraction is exact since T ≥ 7
--   - encoding: noiseless oracle g(x; ξ) = ∇f(x) almost surely → Noiseless f g μ: for every x, g x ξ = ∇f(x) for μ-a.e. ξ; reason: fresh samples at every query make this the paper's almost-sure exactness at adaptive points; same instances
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41001434449aea8ba3a6ba5d66658a8f94ea9ffeebad36bbb903374006), §4, Theorem 1, eq. (9), p.6 (proof App. A, pp.12–16)

import Mathlib
import Definitions.Def_AnytimeAdaVR_Assumption1
import Definitions.Def_AnytimeAdaVR_Assumption2
import Definitions.Def_AnytimeAdaVR_AvgSmooth
import Definitions.Def_AnytimeAdaVR_Noiseless
import Definitions.Def_AnytimeAdaVR_tapeMeasure
import Definitions.Def_AnytimeAdaVR_Supplement_alg1Run

namespace AnytimeAdaVR.Supplement

open AnytimeAdaVR MeasureTheory

/-- **Theorem 1 (fixed-budget guarantees in three regimes).** Jiang–Wang–Yang–Zhang–Li, *Adaptive
Variance Reduction across Smoothness and Noise Conditions* (preprint, 2026), §4, Theorem 1, eq. (9),
p.6: "Suppose Assumptions 1 and 2 hold. For any integer T ≥ 7, let n = ⌊T/7⌋. Algorithm 1 uses
7n − 1 ≤ T gradient evaluations and returns x̂_T with the following guarantees.
E‖∇f(x̂_T)‖ ≤ (∆f + 3L + 7σ)n^{−1/4} under the two basic assumptions,
(∆f + 3L + 3L̄ + 12σ)n^{−1/3} under average smoothness as well, (∆f + 4L)n^{−1/2} for noiseless
gradients. The algorithm does not use L, L̄, σ, ∆f, or the applicable oracle condition."

For every dimension `d`, probability space of samples `(Ξ, μ)`, objective `f`, jointly measurable
stochastic gradient `g`, initial point `xinit` and constants `L, ∆f, σ` with Assumptions 1 and 2,
and every integer `T ≥ 7` with `n = ⌊T/7⌋`: on every tape, Algorithm 1 (`alg1Run`) makes exactly
`7n − 1` gradient evaluations, `7n − 1 ≤ T`, and its output `x̂_T` satisfies all three bounds —
the basic one, the average-smooth one for every `L̄` with Assumption 3, and the noiseless one.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. `Id.run ((alg1Run g xinit T ω).run 0)`
is the pair (output, number of gradient evaluations) on the tape `ω`. Expectations are lower
integrals of `‖·‖ₑ` over `tapeMeasure μ`, compared with `ENNReal.ofReal` of the bound. -/
theorem theorem_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (L Δf σ : ℝ)
    (hg : Measurable (Function.uncurry g)) (h1 : Assumption1 f L Δf xinit)
    (h2 : Assumption2 f g μ σ) (T : ℕ) (hT : 7 ≤ T) :
    (∀ ω : Tape Ξ, (Id.run ((alg1Run g xinit T ω).run 0)).2 = 7 * (T / 7) - 1) ∧
    7 * (T / 7) - 1 ≤ T ∧
    (∫⁻ ω, ‖gradient f (Id.run ((alg1Run g xinit T ω).run 0)).1‖ₑ ∂(tapeMeasure μ) ≤
      ENNReal.ofReal ((Δf + 3 * L + 7 * σ) * ((T / 7 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)))) ∧
    (∀ Lbar : ℝ, AvgSmooth g μ Lbar →
      ∫⁻ ω, ‖gradient f (Id.run ((alg1Run g xinit T ω).run 0)).1‖ₑ ∂(tapeMeasure μ) ≤
        ENNReal.ofReal ((Δf + 3 * L + 3 * Lbar + 12 * σ) * ((T / 7 : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
    (Noiseless f g μ →
      ∫⁻ ω, ‖gradient f (Id.run ((alg1Run g xinit T ω).run 0)).1‖ₑ ∂(tapeMeasure μ) ≤
        ENNReal.ofReal ((Δf + 4 * L) * ((T / 7 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))) := by sorry

end AnytimeAdaVR.Supplement
