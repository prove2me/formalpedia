-- Prove2me | Theorems.Thm_CompetingAgents_lemma_33_corrected
-- name    : CompetingAgents.lemma_33_corrected
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:56.81249+00:00
-- url     : https://prove2.me/theorems/793c95e0-5016-4b4b-be40-32e7725988da
-- title:
--   Lemma 33 (corrected: the one-step bound $P(|q(P^n(\beta,\hat S^t_n))-q(P(\beta,\hat S^t_n))|\ge\lambda)\le4e^{-2nM_\lambda^2}$ at the random threshold)
-- statement:
--   Suppose Assumptions 1, 2, 3 and $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$, let $\beta\in\mathcal B$, and let $(\hat S^t_n)_{t\ge0}$ be the process (4.1) driven by fresh i.i.d. cohorts from an initial threshold $\hat S^0_n\in\mathbb R$. Then for every $\lambda>0$ and every $t\ge0$,
--
--   $$P\Big(\big|q\big(P^n(\beta,\hat S^t_n)\big)-q\big(P(\beta,\hat S^t_n)\big)\big|\ge\lambda\Big)\le4e^{-2nM_\lambda^2},$$
--
--   where $q(P^n(\beta,\hat S^t_n))=\hat S^{t+1}_n$ is the next threshold.
--
--   The printed Lemma 33 asserts that a random variable $z^t$, equal to $\lambda_g$ with probability $p_n(\lambda_g)$ and to $C_k$ with probability $(1-p_n(\lambda_g))/2^k$, stochastically dominates this error at every fixed $s$. That is false (see the correction below). What the proof of Theorem 4 uses at (I.25) is the atom of $z^t$ at $\lambda_g$, applied at the random threshold $\hat S^t_n$; this is that statement, for every $\lambda>0$.
--
--   Differences from the source:
--
--   - correction: $z^t$ (equal to $\lambda_g$ w.p. $p_n(\lambda_g)$, to $C_k$ w.p. $(1-p_n(\lambda_g))/2^k$) stochastically dominates $|q(P^n(\beta,s))-q(P(\beta,s))|$ for every $s$ → $P(|q(P^n(\beta,\hat S^t_n))-q(P(\beta,\hat S^t_n))|\ge\lambda)\le4e^{-2nM_\lambda^2}$ for every $\lambda>0$ and $t$; reason: the printed lemma is false; counterexample: $d=1$, $\beta=1$, $\mathcal X=[-10,10]$, $q=1/2$; two types, $Z_A=0$ with weight $0.6$ and $Z_B=4$ with weight $0.4$; $c(y)=\alpha y^2/2$, $\alpha=10^6$, $\sigma=0.01$ (all of Assumptions 1–3 and the noise bound of Theorem 4 hold). For $\lambda=1/2$ and $n=1000$, the printed $z^t$ gives $P(z^t\ge3)\approx2.4\cdot10^{-78}$, while $|q(P^n(\beta,s))-q(P(\beta,s))|\ge3$ whenever at most $499$ agents are of type A, an event of probability about $6.7\cdot10^{-11}$. Its proof treats $M_b$ as $M_{\lambda_g}b$, but $M_b\le\min(q,1-q)$. The corrected statement is the part Theorem 4 uses
--   - generalization: the conditions of Theorem 4, including $\sigma^2>2/(\alpha_*\sqrt{2\pi e})$ → Assumptions 1–3 and $\sigma^2>1/(\alpha_*\sqrt{2\pi e})$; reason: the weaker noise condition of Lemma 3 suffices; the conditions of Theorem 4 imply it
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: the process (4.1); the running text of p.9 prints $\hat S^t_n=q(P^{n,t-1})$ → display (4.1): $\hat S^t_n=q(P^n(\beta,\hat S^{t-1}_n))$, where cohort $t$ is a fresh sample, independent over all $(t,j)$, each agent with law $F$, responding to the realized $\hat S^{t-1}_n$; reason: display (4.1) is the definition and the text says that $n$ new agents are sampled i.i.d. at each step
--   - encoding: a sample of $n\ge1$ agents (implicit) → every $n\in\mathbb N$; reason: at $n=0$ the Lean bound is $4$, trivially true
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 33, pp.35–36, as used at (I.25), p.54

import Mathlib
import Definitions.Def_CompetingAgents_thresholdProcess

open MeasureTheory ProbabilityTheory

namespace CompetingAgents

/-- Lemma 33, corrected (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5,
Lemma 33, pp.35–36, as used at (I.25), p.54). Suppose Assumptions 1, 2, 3 and
`σ² > 1/(α_*√(2πe))`, and let `Ŝⁿₜ` be the process (4.1) driven by fresh i.i.d. cohorts. For every
`λ > 0` and every `t ≥ 0`, the one-step error at the random threshold `Ŝⁿₜ` satisfies
`P(|q(Pⁿ(β, Ŝⁿₜ)) − q(P(β, Ŝⁿₜ))| ≥ λ) ≤ 4 exp(−2n M_λ²)`.

**Formalization Note.** The printed Lemma 33 (stochastic dominance by a variable `zᵗ` with atoms
`C_k`) is false; this is the part of it that the proof of Theorem 4 uses, the atom at `λ`, applied at
the random threshold `Ŝⁿₜ` as in (I.25). `q(Pⁿ(β, Ŝⁿₜ))` is `Ŝⁿₜ₊₁` by (4.1). At `n = 0` the bound
is `4` and holds trivially. -/
theorem lemma_33_corrected {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι] (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (hσ : 1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (S0 : ℝ) (A : ℕ → Fin n → Ω → ι × Cov d) (hA : IsFreshCohorts M μ A)
    (lam : ℝ) (hlam : 0 < lam) (t : ℕ) :
    μ {ω | lam ≤ |thresholdProcess M β n S0 A (t + 1) ω -
        eqMap M β (thresholdProcess M β n S0 A t ω)|} ≤
      ENNReal.ofReal (4 * Real.exp (-2 * n * Mlam M β lam ^ 2)) := by sorry

end CompetingAgents
