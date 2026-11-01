-- Prove2me | Theorems.Thm_CompetingAgents_lemma_31
-- name    : CompetingAgents.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:34.262639+00:00
-- url     : https://prove2.me/theorems/96a06189-00d9-4169-b3a8-38491574edc1
-- title:
--   Lemma 31 — $\partial q(P(\beta,s))/\partial s<1$, and $|\partial q(P(\beta,s))/\partial s|<\bar\kappa$ under more noise
-- statement:
--   Fix $\beta\in\mathcal B$ and $\bar\kappa\in(0,1]$, and suppose Assumptions 1, 2 and 3 hold.
--
--   1. If $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$, then at every $s$ the population quantile map is differentiable and
--   $$\frac{\partial q(P(\beta,s))}{\partial s}<1.$$
--   2. If $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}\cdot\frac{\bar\kappa+1}{\bar\kappa}$, then at every $s$
--   $$\left|\frac{\partial q(P(\beta,s))}{\partial s}\right|<\bar\kappa.$$
--
--   The first bound gives uniqueness of the equilibrium threshold; the second makes the quantile map a contraction.
--
--   **Formalization Note** The derivative is asserted to exist at every $s$, so the bounds are never about a default value.
--
--   Differences from the source:
--
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: the last bound is printed $|\partial q(P(\beta,s))/\partial s|<\kappa$ → $|\partial q(P(\beta,s))/\partial s|<\bar\kappa$; reason: $\kappa$ is not defined in Lemma 31, whose only constant is $\bar\kappa$; the proof on p.51 and the use on p.35 bound by $\bar\kappa$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 31, p.33

import Mathlib
import Definitions.Def_CompetingAgents_scoreCDF

namespace CompetingAgents

/-- Lemma 31 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 31,
p.33). Fix `β ∈ 𝔅`, `κ̄ ∈ (0, 1]`, and suppose Assumptions 1, 2 and 3 hold. If
`σ² > 1/(α_*√(2πe))`, then `∂q(P(β, s))/∂s < 1`. If `σ² > (1/(α_*√(2πe)))·(κ̄+1)/κ̄`, then
`|∂q(P(β, s))/∂s| < κ̄`.

**Formalization Note.** The derivative is asserted to exist (`HasDerivAt`) at every `s`, so the
bounds are not about Lean's junk derivative `0`. The page prints `κ` in the last bound; `κ̄` is meant
(it is the only constant in the statement, and the proof on p.51 bounds by `κ̄`). -/
theorem lemma_31 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1) :
    (1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2 →
      ∀ s : ℝ, ∃ g' : ℝ, HasDerivAt (eqMap M β) g' s ∧ g' < 1) ∧
    (∀ κbar : ℝ, 0 < κbar → κbar ≤ 1 →
      1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) * ((κbar + 1) / κbar) < M.σ ^ 2 →
      ∀ s : ℝ, ∃ g' : ℝ, HasDerivAt (eqMap M β) g' s ∧ |g'| < κbar) := by sorry

end CompetingAgents
