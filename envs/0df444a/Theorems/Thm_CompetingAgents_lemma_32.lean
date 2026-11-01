-- Prove2me | Theorems.Thm_CompetingAgents_lemma_32
-- name    : CompetingAgents.lemma_32
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:28.41655+00:00
-- url     : https://prove2.me/theorems/7c1e66bd-3f5e-4432-9a53-3569f993bc12
-- title:
--   Lemma 32 — $P(\beta,s)$ and $q(P(\beta,s))$ converge to the raw score law and its quantile as $s\to\pm\infty$
-- statement:
--   Let $\beta\in\mathcal B$ and let $P$ be the distribution function of $\beta^T(Z_i+\epsilon_i)$, where $(Z_i,c_i,\epsilon_i)\sim F$. Under Assumptions 1, 2, 3, if $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$, then for every $r$
--
--   $$P(\beta,s)(r)\to P(r)\quad\text{as }s\to\infty\text{ and as }s\to-\infty,$$
--
--   and
--
--   $$\lim_{s\to\infty}q(P(\beta,s))=q(P),\qquad\lim_{s\to-\infty}q(P(\beta,s))=q(P).$$
--
--   Far from any agent's peak, agents stop modifying their covariates, so the population threshold returns to that of the unmodified scores. This controls $q(P(\beta,s))$ uniformly in $s$, which is what makes $M_\lambda>0$ in Lemma 3.
--
--   Differences from the source:
--
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 32, p.33

import Mathlib
import Definitions.Def_CompetingAgents_scoreCDF

open Filter Topology

namespace CompetingAgents

/-- Lemma 32 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 32,
p.33). Let `β ∈ 𝔅` and let `P` be the distribution of `βᵀ(Zᵢ + εᵢ)` with `(Zᵢ, cᵢ, εᵢ) ∼ F`. Under
Assumptions 1, 2 and 3, if `σ² > 1/(α_*√(2πe))`, then `P(β, s)` converges pointwise to `P` as
`s → ∞` and as `s → −∞`, and `lim_{s→±∞} q(P(β, s)) = q(P)`.

**Formalization Note.** `P` is `rawScoreCDF`, the distribution function of the unmodified scores;
pointwise convergence is convergence of the distribution functions at every `r ∈ ℝ`. -/
theorem lemma_32 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (hσ : 1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1) :
    (∀ r : ℝ, Tendsto (fun s => scoreCDF M β s r) atTop (𝓝 (rawScoreCDF M β r)) ∧
      Tendsto (fun s => scoreCDF M β s r) atBot (𝓝 (rawScoreCDF M β r))) ∧
    Tendsto (eqMap M β) atTop (𝓝 (quantile M.lev (rawScoreCDF M β))) ∧
    Tendsto (eqMap M β) atBot (𝓝 (quantile M.lev (rawScoreCDF M β))) := by sorry

end CompetingAgents
