-- Prove2me | Theorems.Thm_CompetingAgents_lemma_27
-- name    : CompetingAgents.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:24:53.514985+00:00
-- url     : https://prove2.me/theorems/727dc413-a55a-49b7-b92d-c425b8d6f9a4
-- title:
--   Lemma 27 — the expected utility is $C^2$, strictly concave in $x$, and maximized where its gradient vanishes
-- statement:
--   Under Assumption 1, the expected utility $\mathbb E_\epsilon[U_i(x;\beta,s)]$ of (2.2) is twice continuously differentiable jointly in $(x,\beta,s)$. If moreover
--
--   $$\sigma^2>\frac{1}{\alpha_i\sqrt{2\pi e}},$$
--
--   then for every $\beta\in\mathcal B$ and $s\in\mathbb R$ it is strictly concave in $x$, and for every $x\in\mathrm{Int}(\mathcal X)$
--
--   $$x=x_i^*(\beta,s)\iff\nabla_x\mathbb E_\epsilon[U_i(x;\beta,s)]=0.$$
--
--   This is the regularity behind Proposition 1: strict concavity gives uniqueness of the best response, and the first-order condition allows the implicit function theorem.
--
--   Differences from the source:
--
--   - generalization: $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$, $\mathcal C$ convex and compact (p.6) → any cost function satisfying Assumption 1; reason: the statement does not use $\mathcal C$; every cost function of the source satisfies Assumption 1
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: Lemma 27 does not restate the domain of $\beta$ → $\beta\in\mathcal B$ in the concavity and first-order claims; all $\beta\in\mathbb R^d$ in the smoothness claim; reason: the paper's criteria are $\beta\in\mathcal B=\mathbb S^{d-1}$ (p.5); for large $\|\beta\|$ concavity fails
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Lemma 27, p.31

import Mathlib
import Definitions.Def_CompetingAgents_bestResponse

namespace CompetingAgents

/-- Lemma 27 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5, Lemma 27,
p.31). Under Assumption 1, the expected utility `E_ε[Uᵢ(x; β, s)]` is twice continuously
differentiable in `(x, β, s)`. If moreover `σ² > 1/(αᵢ√(2πe))`, it is strictly concave in `x`; and
if additionally `x ∈ Int(𝒳)`, then `x = x*ᵢ(β, s)` if and only if `∇ₓ E_ε[Uᵢ(x; β, s)] = 0`.

**Formalization Note.** Expected utility is formula (2.2) (`expectedUtility`). The criterion `β`
ranges over the unit sphere `𝔅 = 𝕊^{d−1}` in the second and third claims, as everywhere in the paper
(p.5); the smoothness claim is stated for all `β ∈ ℝ^d`. The gradient condition is `fderiv = 0`.
Strict concavity is on all of `ℝ^d`. -/
theorem lemma_27 {d : ℕ} {ι : Type*} [Fintype ι] (M : Model d ι) (hA1 : Assumption1 M) (i : ι) :
    ContDiff ℝ 2 (fun p : Cov d × Cov d × ℝ => expectedUtility M i p.2.1 p.2.2 p.1) ∧
    (1 / (M.α i * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2 →
      ∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ s : ℝ,
        StrictConcaveOn ℝ Set.univ (expectedUtility M i β s) ∧
        ∀ x ∈ interior M.X,
          (x = bestResponse M i β s ↔ fderiv ℝ (expectedUtility M i β s) x = 0)) := by sorry

end CompetingAgents
