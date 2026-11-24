-- Prove2me | Theorems.Thm_Curvature_contextualSearch
-- name    : Curvature.contextualSearch
-- status  : Open
-- author  : @ssakaue
-- created : 2026-11-24T07:25:43.526846+00:00
-- url     : https://prove2.me/theorems/684f7c0e-9edb-4b53-b021-a75cae8e3349
-- title:
--   Corollary 7 — contextual search with comparison noise
-- statement:
--   Let $d\ge1$ and $\kappa\in(0,1]$. In contextual search with noisy comparisons, a target $u\in\mathbb B_2^d$ is unknown to the learner. In round $t$, the learner first sees a context $\phi_t\in\mathbb B_2^d$, then predicts $\widehat y_t$ for the response $y_t^\star\coloneqq\langle\phi_t,u\rangle$, and finally observes a comparison bit $Y_t\in\{-1,1\}$ that reports the sign of $\widehat y_t-y_t^\star$, possibly with an error. Let $\omega_{\psi_1}(\mathbb B_2^d)$ be the maximal subexponential mean width of the unit ball, the supremum of $\mathbb E\lVert Z\rVert_2$ over random vectors $Z$ in $\mathbb R^d$ with $\mathbb EZ=0$ and $\mathbb E\exp|\langle v,Z\rangle|\le2$ for every $v\in\mathbb B_2^d$. The statement has three parts.
--
--   1. **Width.** $\omega_{\psi_1}(\mathbb B_2^d)\le2\sqrt d$.
--
--   2. **Upper bound for a fixed target under conditional noise.** Fix a target $u\in\mathbb B_2^d$. Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space on which the contexts $\phi_t$ and the bits $Y_t$ are random variables, and let $W,A>0$ satisfy $\omega_{\psi_1}(\mathbb B_2^d)\le W\le A\sqrt d$. Run Algorithm 5 on $\mathbb B_2^d$ with $G=1$, the bound $W$, any weight rule satisfying the paper's approximation condition, and base learners using the fixed initialization of the Euclidean ball in standard coordinates. Its prediction $w_t\in\mathbb B_2^d$ is computed from the inputs $Y_s\phi_s$ of the rounds $s<t$, and the learner predicts $\widehat y_t\coloneqq\langle\phi_t,w_t\rangle$; the rule uses neither $u$ nor $\kappa$. Suppose that there are a filtration $(\mathcal F_t)$ and signs $\sigma_t\in\{-1,1\}$ such that $\phi_t$, $\widehat y_t$ and $\sigma_t$ are $\mathcal F_t$-measurable, $Y_t$ is $\mathcal F_{t+1}$-measurable with values in $\{-1,1\}$, $\sigma_t(\widehat y_t-y_t^\star)=|\widehat y_t-y_t^\star|$ (either sign is allowed at a tie), and
--   $$
--   \mathbb P\bigl(Y_t=\sigma_t\bigm|\mathcal F_t\bigr)\ge\frac{1+\kappa}{2}\quad\text{almost surely.}
--   $$
--   Let $C\coloneqq24\bigl(393216+514/\log2\bigr)$ and $B\coloneqq(2C+C^2)A\sqrt d/\kappa^2$. Then, for every horizon $T$, the cumulative error $\sum_{t=1}^T|\widehat y_t-y_t^\star|$ is integrable and
--   $$
--   \mathbb E\Bigl[\sum_{t=1}^T\bigl|\widehat y_t-y_t^\star\bigr|\Bigr]\le B,\qquad\text{so}\qquad\sup_{T\ge1}\mathbb E\Bigl[\sum_{t=1}^T\bigl|\widehat y_t-y_t^\star\bigr|\Bigr]\le B.
--   $$
--
--   3. **Lower bound for every learner under independent flips.** For every learner of the kind described below, there is a target $u\in\mathbb B_2^d$ for which
--   $$
--   \mathbb E\Bigl[\sum_{t=1}^{dn}\bigl|\widehat y_t-y_t^\star\bigr|\Bigr]\ge\frac{\sqrt d}{64\kappa^2},\qquad\text{where }n\coloneqq\max\bigl\{1,\lfloor1/(16\kappa^2)\rfloor\bigr\}.
--   $$
--   The contexts are fixed in advance: $e_1$ for $n$ rounds, then $e_2$ for $n$ rounds, and so on up to $e_d$, where $e_i$ is the $i$-th standard basis vector. The correct bit is $+1$ exactly when the prediction is at least the response. The learner observes its opposite with probability $(1-\kappa)/2$ and the correct bit otherwise. The flip decisions are independent across rounds and independent of the learner's seed, with the same probability for every target. The learner predicts a value in $[-1,1]$ from a private seed, the earlier bits and the contexts up to the current round, and for each fixed history of bits and contexts its prediction is a measurable function of the seed. The expectation is taken over the seed and the flips.
--
--   The upper bound assumes only the lower bound on the conditional probability of a correct bit; the matching lower bound uses the stronger model of independent flips. For $W\le A\sqrt d$, the Lean bound uses $(2C+C^2)A$ as the factor multiplying $\sqrt d/\kappa^2$ in the upper bound on the expected cumulative absolute error. The paper leaves this factor implicit.
-- source:
--   arXiv:2611.27572v1, Corollary 7, p. 14. https://arxiv.org/html/2611.27572v1#Thmtheorem7

import Definitions.Def_Curvature_ContextualSearch

set_option autoImplicit false
noncomputable section
open Curvature
open MeasureTheory
universe u v
open Curvature.ContextualSearch

theorem Curvature.contextualSearch {d : ℕ} (hd : 0 < d) {κ : ℝ} (hk : 0 < κ) (hk' : κ ≤ 1) :
    coordinateWidth (searchUnitBall d) ≤ 2*Real.sqrt d ∧
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {W A : ℝ} (_ : 0 < W) (_ : coordinateWidth (searchUnitBall d) ≤ W)
      (_ : W ≤ A*Real.sqrt d) (P : AdaptiveWeightRule (adaptiveWidthScale 1 W))
      (u : searchUnitBall d) (φ : ℕ → Ω → searchUnitBall d) (Y : ℕ → Ω → ℝ),
      let yhat := fun t ω => predictedResponse (searchUnitBall_initialization hd) P
        (fun s => φ s ω) (fun s => Y s ω) t
      ComparisonNoise μ κ u φ Y yhat →
      let err := fun T ω => ∑ t ∈ Finset.range T, |yhat t ω - dotProduct (φ t ω).val u.val|
      let B := (2*adaptiveWidthConstant + adaptiveWidthConstant^2) * A * Real.sqrt d / κ^2
      (∀ T, Integrable (err T) μ ∧ (∫ ω, err T ω ∂μ) ≤ B) ∧ (⨆ T : ℕ, ∫ ω, err T ω ∂μ) ≤ B) ∧
    (∀ {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (L : ContextLearner d Ω),
      let ctx := coordinateSchedule d (searchBlockLength κ)
      0 < ctx.length ∧ (∀ x ∈ ctx, x ∈ searchUnitBall d) ∧
        ∃ u ∈ searchUnitBall d, Real.sqrt d / (64*κ^2) ≤ expectedError μ L κ ctx u) := by sorry
