-- Prove2me | Theorems.Thm_CompetingAgents_proposition_1
-- name    : CompetingAgents.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:06.827406+00:00
-- url     : https://prove2.me/theorems/dd367038-634b-4fc0-922a-290ca2d9950e
-- title:
--   Proposition 1 — the best response exists, is unique and $C^1$, and $\omega_i$ is a contraction under more noise
-- statement:
--   Let $\beta\in\mathcal B$, $s\in\mathbb R$, $\bar\kappa\in(0,1]$, and suppose Assumption 1 holds.
--
--   1. The best response $x_i^*(\beta,s)$ exists: the expected utility has a maximizer over $\mathcal X$.
--   2. If moreover $\sigma^2>1/(\alpha_i\sqrt{2\pi e})$, the maximizer is unique, and $x_i^*$ is continuously differentiable in $(\beta,s)$ at every point where $x_i^*(\beta,s)\in\mathrm{Int}(\mathcal X)$.
--   3. If
--   $$\sigma^2>\frac{1}{\alpha_i\sqrt{2\pi e}}\cdot\frac{\bar\kappa+1}{\bar\kappa}$$
--   for some $\bar\kappa\in(0,1]$, then there is $\kappa<\bar\kappa$ such that the expected score $\omega_i(s;\beta)=\beta^Tx_i^*(\beta,s)$ is $\kappa$-Lipschitz in $s$ for every $\beta\in\mathcal B$.
--
--   This is the agent-level foundation of the mean-field results: enough noise makes the best response smooth, and more noise makes the expected score a contraction.
--
--   Differences from the source:
--
--   - generalization: $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$, $\mathcal C$ convex and compact (p.6) → any cost function satisfying Assumption 1; reason: the statement does not use $\mathcal C$; every cost function of the source satisfies Assumption 1
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: continuously differentiable in $\beta$ → $C^1$ within $\mathcal B\times\mathbb R$, i.e. on the sphere; reason: only $\beta\in\mathcal B=\mathbb S^{d-1}$ belongs to the model (p.5)
--   - reading: Lipschitz constant less than $\bar\kappa$ for any $\beta\in\mathcal B$ → one constant $\kappa<\bar\kappa$ that serves every $\beta\in\mathcal B$; reason: the uniform reading is the stronger one, and the bound derived from the noise condition does not depend on $\beta$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Proposition 1, p.7

import Mathlib
import Definitions.Def_CompetingAgents_bestResponse

open scoped NNReal

namespace CompetingAgents

/-- Proposition 1 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5,
Proposition 1, p.7). Let `β ∈ 𝔅`, `s ∈ ℝ`, `κ̄ ∈ (0, 1]`. Under Assumption 1 the best response
`x*ᵢ(β, s)` exists. If moreover `σ² > 1/(αᵢ√(2πe))`, then `x*ᵢ(β, s)` is unique and continuously
differentiable in `(β, s)` whenever `x*ᵢ(β, s) ∈ Int(𝒳)`. Finally, if
`σ² > (1/(αᵢ√(2πe)))·(κ̄+1)/κ̄` for some `κ̄ ∈ (0, 1]`, the expected score
`ωᵢ(s; β) = βᵀ x*ᵢ(β, s)` is a contraction in `s` with Lipschitz constant less than `κ̄`, for any
`β ∈ 𝔅`.

**Formalization Note.** Existence is of a maximizer of (2.2) over `𝒳`; uniqueness is that any two
maximizers coincide; continuous differentiability is `C¹` within `𝔅 × ℝ` at every `(β, s)` whose best
response is interior, because only `β ∈ 𝔅 = 𝕊^{d−1}` belongs to the model. "Lipschitz constant less
than `κ̄` for any `β`" is read uniformly: one constant `κ < κ̄` serves every `β ∈ 𝔅`. -/
theorem proposition_1 {d : ℕ} {ι : Type*} [Fintype ι] (M : Model d ι) (hA1 : Assumption1 M)
    (i : ι) :
    (∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ,
      ∃ x ∈ M.X, IsMaxOn (expectedUtility M i β s) M.X x) ∧
    (1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2 →
      (∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ, ∀ x ∈ M.X, ∀ y ∈ M.X,
        IsMaxOn (expectedUtility M i β s) M.X x → IsMaxOn (expectedUtility M i β s) M.X y →
          x = y) ∧
      ∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ, bestResponse M i β s ∈ interior M.X →
        ContDiffWithinAt ℝ 1 (fun p : Cov d × ℝ => bestResponse M i p.1 p.2)
          (Metric.sphere (0 : Cov d) 1 ×ˢ Set.univ) (β, s)) ∧
    (∀ κbar : ℝ, 0 < κbar → κbar ≤ 1 →
      1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) * ((κbar + 1) / κbar) < M.σ ^ 2 →
      ∃ κ : ℝ≥0, (κ : ℝ) < κbar ∧
        ∀ β ∈ Metric.sphere (0 : Cov d) 1, LipschitzWith κ (fun s => omega M i β s)) := by sorry

end CompetingAgents
