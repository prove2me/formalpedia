-- Prove2me | Theorems.Thm_CompetingAgents_lemma_29
-- name    : CompetingAgents.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:59.911986+00:00
-- url     : https://prove2.me/theorems/75cef181-56fe-4994-9b1d-4e565ae9dfb3
-- title:
--   Lemma 29 — $\omega_i(s;\beta)\to\beta^TZ_i$ as $s\to\pm\infty$, and $\omega_i$ is unimodal
-- statement:
--   Under Assumption 1, if $\sigma^2>1/(\alpha_i\sqrt{2\pi e})$, $\beta\in\mathcal B$ and $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for all $s$, then
--
--   $$\lim_{s\to\infty}\omega_i(s;\beta)=\beta^TZ_i,\tag{E.2}$$
--   $$\lim_{s\to-\infty}\omega_i(s;\beta)=\beta^TZ_i.\tag{E.3}$$
--
--   Moreover there is a point $s^*$ at which $\omega_i(\cdot;\beta)$ attains its maximum; $\omega_i$ is strictly increasing on $s<s^*$ and strictly decreasing on $s>s^*$.
--
--   An agent facing a very low or very high threshold does not modify its covariates. These limits are what keep the population quantile bounded in Lemmas 3 and 32.
--
--   **Formalization Note** The interior hypothesis is assumed at every threshold $s$, for the given $\beta\in\mathcal B$. "Increasing" and "decreasing" are read strictly.
--
--   Differences from the source:
--
--   - generalization: $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$, $\mathcal C$ convex and compact (p.6) → any cost function satisfying Assumption 1; reason: the statement does not use $\mathcal C$; every cost function of the source satisfies Assumption 1
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ → $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$ for every $s\in\mathbb R$, at the given $\beta$; reason: the conclusions range over all thresholds $s$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 29, (E.2)–(E.3), p.31

import Mathlib
import Definitions.Def_CompetingAgents_bestResponse

open Filter Topology
open scoped RealInnerProductSpace

namespace CompetingAgents

/-- Lemma 29 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 29,
(E.2)–(E.3), p.31). Under Assumption 1, if `σ² > 1/(αᵢ√(2πe))` and `x*ᵢ(β, s) ∈ Int(𝒳)`, then
`lim_{s→∞} ωᵢ(s; β) = βᵀZᵢ` and `lim_{s→−∞} ωᵢ(s; β) = βᵀZᵢ`. Moreover `ωᵢ(·; β)` is maximized at a
point `s*`, is increasing for `s < s*` and decreasing for `s > s*`.

**Formalization Note.** The interior condition is assumed at every threshold `s`, for the given
`β ∈ 𝔅`. "Increasing" and "decreasing" are strict. -/
theorem lemma_29 {d : ℕ} {ι : Type*} [Fintype ι] (M : Model d ι) (hA1 : Assumption1 M) (i : ι)
    (hσ : 1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2)
    (β : Cov d) (hβ : β ∈ Metric.sphere (0 : Cov d) 1)
    (hint : ∀ s : ℝ, bestResponse M i β s ∈ interior M.X) :
    Tendsto (fun s => omega M i β s) atTop (𝓝 ⟪β, M.Z i⟫) ∧
    Tendsto (fun s => omega M i β s) atBot (𝓝 ⟪β, M.Z i⟫) ∧
    ∃ sStar : ℝ, IsMaxOn (fun s => omega M i β s) Set.univ sStar ∧
      StrictMonoOn (fun s => omega M i β s) (Set.Iio sStar) ∧
      StrictAntiOn (fun s => omega M i β s) (Set.Ioi sStar) := by sorry

end CompetingAgents
