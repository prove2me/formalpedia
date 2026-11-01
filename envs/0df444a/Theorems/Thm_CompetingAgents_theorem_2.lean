-- Prove2me | Theorems.Thm_CompetingAgents_theorem_2
-- name    : CompetingAgents.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:43.196775+00:00
-- url     : https://prove2.me/theorems/1702300f-5317-47fa-a362-1c5619fff2c6
-- title:
--   Theorem 2 — a unique, $C^1$ mean-field equilibrium threshold $s(\beta)$; contraction and convergence of (3.1)
-- statement:
--   Suppose Assumptions 1, 2 and 3 hold and $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}$.
--
--   1. $q(P(\beta,s))$ is continuously differentiable in $(\beta,s)$ on $\mathcal B\times\mathbb R$.
--   2. For every $\beta\in\mathcal B$ there is a unique $s(\beta)$ with
--   $$s(\beta)=q\big(P(\beta,s(\beta))\big),$$
--   and $\beta\mapsto s(\beta)$ is continuously differentiable on $\mathcal B$.
--   3. If moreover $\sigma^2>\frac{1}{\alpha_*\sqrt{2\pi e}}\cdot\frac{\bar\kappa+1}{\bar\kappa}$ for some $\bar\kappa\in(0,1]$, there is $\kappa<\bar\kappa$ such that $q(P(\beta,\cdot))$ is $\kappa$-Lipschitz for every $\beta\in\mathcal B$, and for every $\beta\in\mathcal B$ the fixed-point iteration (3.1), $S^t=q(P(\beta,S^{t-1}))$, converges to $s(\beta)$ from every initial threshold.
--
--   This is the paper's mean-field result: the equilibrium threshold exists, is unique, and depends smoothly on the policy, which is what the policy-gradient method of §5 differentiates.
--
--   **Formalization Note** The differentiable selection $\beta\mapsto s(\beta)$ is asserted to exist; by uniqueness it is the fixed point at every $\beta\in\mathcal B$.
--
--   Differences from the source:
--
--   - generalization: Assumption 2: the $(Z,c)$-marginal of $F$ has finite support; $c_i\in\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ with $\mathcal C$ convex and compact; outcomes $Y_i(0),Y_i(1)$ (pp.6, 8) → finitely many types $i\in\iota$ with weights $w_i>0$, $\sum_i w_i=1$; no membership in $\mathcal C$ is required and the outcomes are not modelled; reason: no statement of the mission mentions $\mathcal C$ or the outcomes, and the score law does not depend on them; every instance of the source is an instance of the Lean model
--   - encoding: $\mathbb E_\epsilon[U_i(x;\beta,s)]$, the expected utility over $\epsilon\sim N(0,\sigma^2 I_d)$ → formula (2.2), $-c_i(x-Z_i)+1-\Phi_\sigma(s-\beta^Tx)$, taken as the definition; reason: (2.2) is the paper's own evaluation of the expectation; the two agree for $\|\beta\|=1$ (proved in the verification file)
--   - encoding: $x_i^*(\beta,s)=\operatorname{argmax}_{x\in\mathcal X}\mathbb E_\epsilon[U_i(x;\beta,s)]$ → a chosen maximizer over $\mathcal X$ (the point $0$ if there were none); reason: under Assumption 1 a maximizer exists and under the noise condition it is unique (Proposition 1), so in every statement the choice is the argmax
--   - reading: the $q$-th quantile $q(\cdot)$ → the lower quantile $\inf\{r : q\le G(r)\}$; reason: the convention of Shao (2003), cited for Theorem 17; for $P(\beta,s)$ it is the unique inverse of Lemma 30
--   - reading: continuously differentiable in $\beta$ → $C^1$ within $\mathcal B\times\mathbb R$, i.e. on the sphere; reason: only $\beta\in\mathcal B=\mathbb S^{d-1}$ belongs to the model (p.5)
--   - reading: Lipschitz constant less than $\bar\kappa$ for any $\beta\in\mathcal B$ → one constant $\kappa<\bar\kappa$ that serves every $\beta\in\mathcal B$; reason: the uniform reading is the stronger one, and the bound derived from the noise condition does not depend on $\beta$
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, Theorem 2, p.9

import Mathlib
import Definitions.Def_CompetingAgents_scoreCDF

open Filter Topology
open scoped NNReal

namespace CompetingAgents

/-- Theorem 2 (Sahoo, Wager, *Policy Learning with Competing Agents*, arXiv:2204.01884v5,
Theorem 2, p.9). Under Assumptions 1, 2 and 3, and if `σ² > 1/(α_*√(2πe))`, then `q(P(β, s))` is
continuously differentiable in `(β, s)`. For any `β ∈ 𝔅` there is a unique fixed point `s(β)` with
`s(β) = q(P(β, s(β)))`, and `s(β)` is continuously differentiable in `β`. If moreover
`σ² > (1/(α_*√(2πe)))·(κ̄+1)/κ̄` for `κ̄ ∈ (0, 1]`, then for any `β ∈ 𝔅`, `q(P(β, ·))` is a contraction
with Lipschitz constant less than `κ̄`, and the fixed-point iteration (3.1) converges to `s(β)`.

**Formalization Note.** Continuous differentiability in `β` is `C¹` on `𝔅 × ℝ` (resp. on `𝔅`), since
only `β ∈ 𝔅 = 𝕊^{d−1}` belongs to the model; the map `β ↦ s(β)` is any function selecting the fixed
point on `𝔅` (it is unique there). "Lipschitz constant less than `κ̄` for any `β`" is read uniformly:
one `κ < κ̄` serves every `β ∈ 𝔅`. The iteration converges from every real initial threshold. -/
theorem theorem_2 {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (M : Model d ι) (hA1 : Assumption1 M) (hA3 : Assumption3 M)
    (hσ : 1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) < M.σ ^ 2) :
    ContDiffOn ℝ 1 (fun p : Cov d × ℝ => eqMap M p.1 p.2)
      (Metric.sphere (0 : Cov d) 1 ×ˢ Set.univ) ∧
    (∀ β ∈ Metric.sphere (0 : Cov d) 1, ∃! s : ℝ, s = eqMap M β s) ∧
    (∃ sOf : Cov d → ℝ, (∀ β ∈ Metric.sphere (0 : Cov d) 1, sOf β = eqMap M β (sOf β)) ∧
      ContDiffOn ℝ 1 sOf (Metric.sphere (0 : Cov d) 1)) ∧
    (∀ κbar : ℝ, 0 < κbar → κbar ≤ 1 →
      1 / (alphaStar M * Real.sqrt (2 * Real.pi * Real.exp 1)) * ((κbar + 1) / κbar) < M.σ ^ 2 →
      (∃ κ : ℝ≥0, (κ : ℝ) < κbar ∧
        ∀ β ∈ Metric.sphere (0 : Cov d) 1, LipschitzWith κ (eqMap M β)) ∧
      ∀ β ∈ Metric.sphere (0 : Cov d) 1, ∀ sβ : ℝ, sβ = eqMap M β sβ →
        ∀ S0 : ℝ, Tendsto (meanFieldIter M β S0) atTop (𝓝 sβ)) := by sorry

end CompetingAgents
