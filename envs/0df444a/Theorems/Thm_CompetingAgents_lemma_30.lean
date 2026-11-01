-- Prove2me | Theorems.Thm_CompetingAgents_lemma_30
-- name    : CompetingAgents.lemma_30
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:16.138608+00:00
-- url     : https://prove2.me/theorems/6fbbb70a-568d-4559-b006-b9df45666a40
-- title:
--   Lemma 30 — formula (F.1) for $P(\beta,s)$; it is strictly increasing, $C^1$, and has a unique continuous inverse
-- statement:
--   For $\beta\in\mathcal B$, the score distribution is
--
--   $$P(\beta,s)(r)=\int\Phi_\sigma\big(r-\beta^Tx_i^*(\beta,s)\big)\,dF=\sum_i w_i\,\Phi_\sigma\big(r-\omega_i(s;\beta)\big).\tag{F.1}$$
--
--   Under Assumptions 1, 2 and 3, if $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$, then:
--
--   1. $P(\beta,s)(r)$ is strictly increasing in $r$;
--   2. it is continuously differentiable in $(\beta,s,r)$ on $\mathcal B\times\mathbb R\times\mathbb R$;
--   3. it has a unique continuous inverse distribution function $Q:(0,1)\to\mathbb R$.
--
--   The formula expresses the score law as a mixture of shifted normal distribution functions; the regularity is what makes the population quantile $q(P(\beta,s))$ a smooth function.
--
--   **Formalization Note** The integral over $F$ is a finite sum because of Assumption 2. "Well-defined" holds by construction: $P(\beta,s)$ is defined as a distribution function. The inverse is a continuous $Q$ on the open interval with $P(\beta,s)(Q(u))=u$, unique among such maps.
--
--   Differences from the source:
--
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: continuously differentiable in $\beta$ → $C^1$ within $\mathcal B\times\mathbb R$, i.e. on the sphere; reason: only $\beta\in\mathcal B=\mathbb S^{d-1}$ belongs to the model (p.5)
--   - encoding: $P(\beta,s)(r)$ is a well-defined function; a unique continuous inverse distribution function → $P(\beta,s)$ is a function by definition; the inverse is the unique continuous $Q:(0,1)\to\mathbb R$ with $P(\beta,s)(Q(u))=u$; reason: the definition makes well-definedness automatic; a continuous right inverse of a strictly increasing function is its inverse
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 30, (F.1), p.33

import Mathlib
import Definitions.Def_CompetingAgents_scoreCDF

namespace CompetingAgents

/-- Lemma 30 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 30,
(F.1), p.33). The distribution `P(β, s)` is given by `P(β, s)(r) = ∫ Φ_σ(r − βᵀx*ᵢ(β, s)) dF`.
Under Assumptions 1, 2 and 3, if `σ² > 1/(α_*√(2πe))`, then `P(β, s)(r)` is a well-defined
function; it is strictly increasing in `r`, continuously differentiable in `(β, s, r)`, and has a
unique continuous inverse distribution function.

**Formalization Note.** Assumption 2 is the finite type index `ι` with weights `wᵢ`, so the integral
over `F` in (F.1) is the finite sum `∑ᵢ wᵢ Φ_σ(r − ωᵢ(s; β))`. `P(β, s)` is defined as the
distribution function of the scores (`scoreCDF`), so it is a function by construction, and (F.1) is
a claim about it. `β` ranges over `𝔅 = 𝕊^{d−1}`; continuous differentiability in `(β, s, r)` is
`C¹` on `𝔅 × ℝ × ℝ`. The inverse distribution function is a continuous `Q : (0, 1) → ℝ` with
`P(β, s)(Q u) = u`, and it is unique. -/
theorem lemma_30 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) :
    (∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s r : ℝ,
      scoreCDF M β s r = ∑ i, M.w i * noiseCDF M (r - omega M i β s)) ∧
    (Assumption1 M → Assumption3 M →
      1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2 →
      (∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ, StrictMono (scoreCDF M β s)) ∧
      ContDiffOn ℝ 1 (fun p : Cov d × ℝ × ℝ => scoreCDF M p.1 p.2.1 p.2.2)
        (Metric.sphere (0 : Cov d) 1 ×ˢ Set.univ) ∧
      ∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ,
        ∃! Q : Set.Ioo (0 : ℝ) 1 → ℝ, Continuous Q ∧ ∀ u, scoreCDF M β s (Q u) = u) := by sorry

end CompetingAgents
