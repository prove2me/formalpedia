-- Prove2me | Theorems.Thm_CompetingAgents_lemma_3
-- name    : CompetingAgents.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:52.395074+00:00
-- url     : https://prove2.me/theorems/cfbe8478-5604-47e0-b947-294f63796ef6
-- title:
--   Lemma 3 — $M_\lambda>0$, $M_\lambda$ is linear as $\lambda\to0$, and $P(|q(P(\beta,s))-q(P^n(\beta,s))|<\lambda)\ge1-4e^{-2nM_\lambda^2}$
-- statement:
--   Fix $\beta\in\mathcal B$ and, for $\lambda>0$, let $M_\lambda$ be as in (4.2). Under Assumptions 1, 2, 3, if $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$, then
--
--   1. $M_\lambda>0$ for every $\lambda>0$;
--   2. $M_\lambda$ is approximately linear in $\lambda$ as $\lambda\to0$: there is $L>0$ with $M_\lambda/\lambda\to L$ as $\lambda\to0^+$;
--   3. for every $\lambda>0$, every threshold $s$ and every sample of $n$ agents drawn i.i.d. from $F$,
--   $$P\big(|q(P(\beta,s))-q(P^n(\beta,s))|<\lambda\big)\ge1-4e^{-2nM_\lambda^2}.$$
--
--   The bound does not depend on $s$; this uniformity is what lets it be applied at the random thresholds of the process (4.1).
--
--   **Formalization Note** The sample is any family of $n$ measurable, independent random agents with law $F$ on any probability space, and $P^n(\beta,s)$ is the empirical distribution function of their scores.
--
--   Differences from the source:
--
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: $M_\lambda$ is approximately linear in $\lambda$ when $\lambda\to0$ → $M_\lambda/\lambda$ converges to some $L>0$ as $\lambda\to0^+$; reason: the strongest precise reading of the phrase; it holds with $L$ the infimum over $s$ of the score density at $q(P(\beta,s))$
--   - encoding: a sample of $n\ge1$ agents (implicit) → every $n\in\mathbb N$; reason: at $n=0$ the source's $P^n$ is undefined and the Lean bound reads $\ge-3$, which is trivially true
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 3, (4.2), p.10

import Mathlib
import Definitions.Def_CompetingAgents_thresholdProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace CompetingAgents

/-- Lemma 3 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 3,
(4.2), p.10). Fix `β ∈ 𝔅`. For `λ > 0` let
`M_λ = inf_{s ∈ ℝ} min{P(β,s)(q(P(β,s)) + λ) − q, q − P(β,s)(q(P(β,s)) − λ)}`. Under Assumptions 1,
2, 3, if `σ² > 1/(α_*√(2πe))`, then `M_λ > 0`, `M_λ` is approximately linear in `λ` as `λ → 0`, and
`P(|q(P(β, s)) − q(Pⁿ(β, s))| < λ) ≥ 1 − 4 exp(−2n M_λ²)`.

**Formalization Note.** "Approximately linear in `λ` when `λ → 0`" is read as: `M_λ / λ` converges to
a positive limit as `λ → 0⁺`. The concentration bound holds for every `λ > 0`, every threshold `s`,
every sample size `n` and every i.i.d. sample `a₀, …, a_{n−1}` of agents with law `F` on any
probability space; `Pⁿ(β, s)` is the empirical distribution function of their scores. At `n = 0` the
right side is `−3` and the bound is trivial. -/
theorem lemma_3 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (hσ : 1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1) {Ω : Type*} [MeasurableSpace Ω] :
    (∀ lam : ℝ, 0 < lam → 0 < Mlam M β lam) ∧
    (∃ L : ℝ, 0 < L ∧ Tendsto (fun lam => Mlam M β lam / lam) (𝓝[>] 0) (𝓝 L)) ∧
    ∀ lam : ℝ, 0 < lam → ∀ (s : ℝ) (n : ℕ) (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ a : Fin n → Ω → ι × Cov d, (∀ j, Measurable (a j)) → iIndepFun a μ →
        (∀ j, μ.map (a j) = agentLaw M) →
        ENNReal.ofReal (1 - 4 * Real.exp (-2 * n * Mlam M β lam ^ 2)) ≤
          μ {ω | |eqMap M β s - quantile M.lev (empiricalScoreCDF M β s fun j => a j ω)| < lam} := by sorry

end CompetingAgents
