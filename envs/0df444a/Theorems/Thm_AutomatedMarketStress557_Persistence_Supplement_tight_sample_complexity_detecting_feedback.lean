-- Prove2me | Theorems.Thm_AutomatedMarketStress557_Persistence_Supplement_tight_sample_complexity_detecting_feedback
-- name    : AutomatedMarketStress557.Persistence.Supplement.tight_sample_complexity_detecting_feedback
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:43:41.805622+00:00
-- url     : https://prove2.me/theorems/0ffb6532-1a12-4b5d-b39a-f93d4b64ff6c
-- title:
--   Theorem 4.5 — Tight sample complexity of detecting the sign of feedback
-- statement:
--   Let the returns follow $r_t=\beta D_{t-1}+s\xi_t$, $D_t=\operatorname{sgn}(r_t)$, for $t\ge1$, where $\xi_1,\xi_2,\ldots$ are independent standard normal variables (Gaussian news, $G=\Phi$), the real initial return $r_0$ is independent of the news with $r_0\neq0$ almost surely and fair initial sign $D_0=\operatorname{sgn}(r_0)$, and
--
--   $$0<|\beta|\le s.$$
--
--   Write $P_\beta$ for the law of the observed path $(r_0,\ldots,r_n)$; the experiments $P_\beta$ and $P_{-\beta}$ use the same initial return and the same news.
--
--   1. **Upper bound.** Let $\hat q=\frac1n\sum_{t=1}^n\mathbf 1[D_t=D_{t-1}]$, and let the test output "herding" ($+1$) iff $\hat q>\tfrac12$, and $-1$ otherwise. For every $\delta>0$ and every $n$ with
--   $$n\ge 9\Big(\frac s\beta\Big)^2\log\frac1\delta,$$
--   the probability that the test's output differs from $\operatorname{sgn}(\beta)$ is at most $\delta$.
--
--   2. **Lower bound.** For every $0<\delta<\tfrac14$, every $n$ with
--   $$n<\frac12\Big(\frac s\beta\Big)^2\log\frac1{4\delta},$$
--   and every measurable, possibly randomized test $\psi$ of the full path $(r_0,\ldots,r_n)$, the error of $\psi$ under $\beta$ or its error under $-\beta$ is larger than $\delta$.
--
--   Logarithms are natural. The two thresholds agree up to a constant factor: the simplest serial statistic, which reads only the signs, detects the direction of feedback with essentially as few observations as any test that sees the full real returns. The theorem is a companion to the mission's goal (Theorem 4.2): marginal statistics cannot distinguish $\beta$ from $-\beta$, while this serial test can, at a quantified cost.
--
--   **Formalization Note** A test is a measurable $\psi:\mathbb R^{n+1}\to[0,1]$ giving the probability of answering "herding"; its error under $\beta>0$ is $\int(1-\psi)\,dP_\beta$ and under $\beta\le0$ is $\int\psi\,dP_\beta$. The lower bound is stated contrapositively: below the threshold, the larger of the two errors exceeds $\delta$.
--
--   Differences from the source:
--   - encoding: D₀ uniform on {±1} for D₀ = sgn(r₀), r₀ independent of the news → r₀ a real random variable independent of the whole news sequence with r₀ ≠ 0 almost surely, and the published Model applied to the initial sign sgn(r₀) with ν the standard Gaussian; reason: the same set of initial laws; the Model's continuity, monotonicity and symmetry clauses hold for Φ and its sign-independence clause follows from the independence of r₀
--   - encoding: "unless n ≥ ½ (s/β)² log(1/(4δ))" → n < ½ (s/β)² log(1/(4δ)) implies the larger of the two errors exceeds δ; reason: the literal contrapositive
--   - generalization: every test that observes the full returns → every measurable ψ from paths to [0,1], the probability of answering herding, with errors defined by integrals; reason: randomized tests are included as well; a deterministic test is the indicator of a measurable set, so the Lean bound specializes to the source's
--   - encoding: the laws P± of (r₀, …, rₙ) under ±β, with the same law of r₀ → pushforwards of P under the observed-path map at β and at −β, for the same r₀ and news; reason: a path law depends only on the joint law of r₀ and the news, so this realizes every pair of experiments with a common initial law
--   - encoding: sgn with sgn(0) unspecified → a sign function with value +1 at 0; reason: every observed return is nonzero almost surely, so no instance changes
--   - encoding: δ with no stated lower bound → 0 < δ in both parts; reason: log(1/δ) and log(1/(4δ)) are defined only for δ > 0, so this excludes only undefined cases
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), Theorem 4.5, PDF pp. 3–4; proof PDF p. 4; equation (3), PDF p. 2; Assumption 1, PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib
import Definitions.Def_AutomatedMarketStress557_Persistence_Model
import Definitions.Def_AutomatedMarketStress557_Persistence_Supplement_FeedbackDetection

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AutomatedMarketStress557.Persistence.Supplement

open AutomatedMarketStress557.Persistence

/-- Theorem 4.5 (Tight sample complexity of detecting feedback), Irene Aldridge,
STOC 2027 submission #557 (October 2026), PDF pp. 3–4. Gaussian news, `0 < |β| ≤ s`.
Upper bound: the sign-agreement test errs with probability at most `δ` once
`n ≥ 9 (s/β)² log(1/δ)`. Lower bound: for `δ < 1/4`, every measurable, possibly
randomized test of the full real path `(r₀, …, rₙ)` has error larger than `δ`
under `β` or under `-β` whenever `n < ½ (s/β)² log(1/(4δ))`. The `±β`
experiments share the initial return and the news. -/
theorem tight_sample_complexity_detecting_feedback {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (r₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ)
    (hE : GaussianExperiment P r₀ ξ) (β s : ℝ) (hβ : 0 < |β|) (hβs : |β| ≤ s) :
    (∀ (n : ℕ) (δ : ℝ), 0 < δ →
      9 * (s / β) ^ 2 * Real.log (1 / δ) ≤ n →
      P.real {ω | agreementTest n (observedPath β s r₀ ξ n ω) ≠ sign β} ≤ δ) ∧
    (∀ (n : ℕ) (δ : ℝ), 0 < δ → δ < 1 / 4 →
      (n : ℝ) < 1 / 2 * (s / β) ^ 2 * Real.log (1 / (4 * δ)) →
      ∀ ψ : (Fin (n + 1) → ℝ) → ℝ, Measurable ψ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
        δ < max (testError P β s r₀ ξ n ψ) (testError P (-β) s r₀ ξ n ψ)) := by sorry

end AutomatedMarketStress557.Persistence.Supplement
