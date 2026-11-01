-- Prove2me | Theorems.Thm_CompetingAgents_lemma_47
-- name    : CompetingAgents.lemma_47
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:17.858104+00:00
-- url     : https://prove2.me/theorems/9649440d-a116-4336-8035-5fac789281fc
-- title:
--   Lemma 47 — the expected score $\omega_i(\cdot;\beta)$ has a unique fixed point
-- statement:
--   Under Assumption 1, if $\sigma^2>1/(\alpha_i\sqrt{2\pi e})$, $\beta\in\mathcal B$ and $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for all $s$, then there is exactly one $s\in\mathbb R$ with
--
--   $$\omega_i(s;\beta)=s.$$
--
--   At this fixed point the agent's expected score equals the threshold; Lemma 29 shows it is where $\omega_i$ peaks.
--
--   **Formalization Note** The interior hypothesis is assumed at every threshold $s$, for the given $\beta\in\mathcal B$.
--
--   Differences from the source:
--
--   - generalization: $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$, $\mathcal C$ convex and compact (p.6) → any cost function satisfying Assumption 1; reason: the statement does not use $\mathcal C$; every cost function of the source satisfies Assumption 1
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ → $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for every $s\in\mathbb R$, at the given $\beta$; reason: the conclusions range over all thresholds $s$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 47, p.49

import Mathlib
import Definitions.Def_CompetingAgents_bestResponse

namespace CompetingAgents

/-- Lemma 47 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 47,
p.49). Under Assumption 1, if `σ² > 1/(αᵢ√(2πe))` and `x*ᵢ(β, s) ∈ Int(𝒳)`, then `ωᵢ(s; β)` has a
unique fixed point.

**Formalization Note.** The interior condition is assumed at every threshold `s`, for the given
`β ∈ 𝔅`, since a fixed point is a statement about all `s`. -/
theorem lemma_47 {d : ℕ} {ι : Type*} [Fintype ι] (M : Model d ι) (hA1 : Assumption1 M) (i : ι)
    (hσ : 1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1)
    (hint : ∀ s : ℝ, bestResponse M i β s ∈ interior M.X) :
    ∃! s : ℝ, omega M i β s = s := by sorry

end CompetingAgents
