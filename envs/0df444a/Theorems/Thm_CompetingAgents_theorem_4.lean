-- Prove2me | Theorems.Thm_CompetingAgents_theorem_4
-- name    : CompetingAgents.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:27:29.475428+00:00
-- url     : https://prove2.me/theorems/79cced2a-bc7a-4e48-b217-7cb73f630695
-- title:
--   Theorem 4 — the finite-agent threshold $\hat S^t_n$ is within $\lambda$ of $s(\beta)$ with probability at least $1-\delta$
-- statement:
--   Fix $\beta\in\mathcal B$ and suppose Assumptions 1, 2 and 3 hold with
--
--   $$\sigma^2>\frac{2}{\alpha_*\sqrt{2\pi e}}.$$
--
--   Then:
--
--   1. the mean-field equilibrium threshold exists and is unique: there is exactly one $s(\beta)$ with $s(\beta)=q(P(\beta,s(\beta)))$;
--   2. $q(P(\beta,\cdot))$ is $\kappa$-Lipschitz for some $\kappa\in(0,1)$;
--   3. let $\kappa\in(0,1)$ be a Lipschitz constant of $q(P(\beta,\cdot))$, $\lambda,\delta\in(0,1)$, $M_\lambda$ as in (4.2), $(\hat S^t_n)$ the process (4.1) driven by fresh i.i.d. cohorts of $n$ agents from a real initial threshold $\hat S^0_n$, and
--   $$\lambda_g=\frac{\lambda(1-\kappa)}{2},\qquad C=|\hat S^0_n-s(\beta)|.$$
--   If
--   $$t\ge\left\lceil\frac{\log\frac{\lambda}{2C}}{\log\kappa}\right\rceil\qquad\text{and}\qquad n\ge\frac{1}{2M_{\lambda_g}^2}\log\frac{4t}{\delta},$$
--   then
--   $$P\big(|\hat S^t_n-s(\beta)|\ge\lambda\big)\le\delta.$$
--
--   This is the paper's finite-sample result: after enough iterations, with enough agents per cohort, the stochastic threshold of the finite system is close to the mean-field equilibrium threshold with high probability. Since $\lambda_g$ is linear in $1-\kappa$ and $M_\lambda$ is linear in small $\lambda$, the required sample size scales with $(1-\kappa)^{-2}$.
--
--   **Formalization Note** The ceiling is compared as an integer. At $C=0$ the source's $\log(\lambda/(2C))$ is undefined; Lean's $\lambda/0=0$ and $\log0=0$ make the $t$-condition $0\le t$, and at $t=0$ the $n$-condition is $0\le n$. The conclusion is true in both cases.
--
--   Differences from the source:
--
--   - generalization: $\kappa$, the Lipschitz constant of $q(P(\beta,\cdot))$; $s(\beta)$, the equilibrium threshold → clauses 1–2 assert that a unique fixed point and some Lipschitz $\kappa\in(0,1)$ exist; clause 3 holds for every Lipschitz constant $\kappa\in(0,1)$ and every fixed point; reason: the least Lipschitz constant lies in $(0,1)$ (Theorem 2 gives $<1$; the map is not constant), so it is one of the $\kappa$ covered, and the fixed point is unique
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: the process (4.1); the running text of p.9 prints $\hat S^t_n=q(P^{n,t-1})$ → display (4.1): $\hat S^t_n=q(P^n(\beta,\hat S^{t-1}_n))$, where cohort $t$ is a fresh sample, independent over all $(t,j)$, each agent with law $F$, responding to the realized $\hat S^{t-1}_n$; reason: display (4.1) is the definition and the text says that $n$ new agents are sampled i.i.d. at each step
--   - encoding: $\hat S^0_n$, some initial threshold; $\lceil\cdot\rceil$; $\log(\lambda/(2C))$ at $C=0$ and $\log(4t/\delta)$ at $t=0$ → $\hat S^0_n$ a real number; the ceiling compared as an integer; Lean's $\lambda/0=0$, $\log0=0$ at the boundaries; reason: the source's formulas are undefined at $C=0$ and $t=0$; Lean's values make the conditions $0\le t$, $0\le n$ there, where the conclusion is true (at $t=0$ the $t$-condition forces $C\le\lambda/2$, and at $C=0$ the bound follows from Lemmas 33–34 corrected)
--   - encoding: cohorts at times $t=1,2,\dots$ → a family indexed by all $t\in\mathbb N$, whose unused cohort $t=0$ is also i.i.d. with law $F$; reason: the cohort $t=0$ does not enter $\hat S^t_n$, and any family of cohorts extends by an independent dummy cohort
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Theorem 4, p.10

import Mathlib
import Definitions.Def_CompetingAgents_thresholdProcess

open MeasureTheory ProbabilityTheory

namespace CompetingAgents

/-- Theorem 4 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Theorem 4,
p.10). Fix `β ∈ 𝔅` and suppose Assumptions 1, 2, 3 hold with `σ² > 2/(α_*√(2πe))`. Let
`λ, δ ∈ (0, 1)`, let `s(β)` be the mean-field equilibrium threshold, `M_λ` as in (4.2), `κ` the
Lipschitz constant of `q(P(β, ·))`, `λ_g = λ(1 − κ)/2` and `C = |Ŝⁿ₀ − s(β)|`. Then for `n, t` with
`t ≥ ⌈log(λ/(2C)) / log κ⌉` and `n ≥ (1/(2M²_{λ_g})) log(4t/δ)`, `P(|Ŝⁿₜ − s(β)| ≥ λ) ≤ δ`.

**Formalization Note.** The statement has three clauses. (1) The fixed point `s(β)` of
`q(P(β, ·))` exists and is unique; (2) `q(P(β, ·))` is `κ`-Lipschitz for some `κ ∈ (0, 1)`; these
make the objects of the theorem well defined. (3) The bound holds for every Lipschitz constant
`κ ∈ (0, 1)` of `q(P(β, ·))` (in particular the least one), every real initial threshold `Ŝⁿ₀ = S0`,
and every process (4.1) driven by measurable cohorts `A t j` of law `F`, independent over all
`(t, j)`, on any probability space. The ceiling is compared as an integer. At `C = 0` Lean's
`λ/0 = 0` and `log 0 = 0` make the `t`-condition `0 ≤ t`, and at `t = 0` the `n`-condition is `0 ≤ n`;
the conclusion is true in both cases. -/
theorem theorem_4 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (hσ : 2 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1) {Ω : Type*} [MeasurableSpace Ω] :
    (∃! s : ℝ, s = eqMap M β s) ∧
    (∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ LipschitzWith (Real.toNNReal κ) (eqMap M β)) ∧
    ∀ κ : ℝ, 0 < κ → κ < 1 → LipschitzWith (Real.toNNReal κ) (eqMap M β) →
    ∀ sβ : ℝ, sβ = eqMap M β sβ →
    ∀ lam δ : ℝ, 0 < lam → lam < 1 → 0 < δ → δ < 1 →
    ∀ (S0 : ℝ) (n t : ℕ) (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ A : ℕ → Fin n → Ω → ι × Cov d, IsFreshCohorts M μ A →
      let lamg := lam * (1 - κ) / 2
      let C := |S0 - sβ|
      ⌈Real.log (lam / (2 * C)) / Real.log κ⌉ ≤ (t : ℤ) →
      1 / (2 * Mlam M β lamg ^ 2) * Real.log (4 * t / δ) ≤ (n : ℝ) →
      μ {ω | lam ≤ |thresholdProcess M β n S0 A t ω - sβ|} ≤ ENNReal.ofReal δ := by sorry

end CompetingAgents
