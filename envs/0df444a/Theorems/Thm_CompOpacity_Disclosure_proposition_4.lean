-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_proposition_4
-- name    : CompOpacity.Disclosure.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:51.874111+00:00
-- url     : https://prove2.me/theorems/a03a9454-d7b7-456d-9f70-9e31e7914be9
-- title:
--   Proposition 4, p. 17 (a < 1/2 in part 2) — unique disclosure equilibrium; competition lowers disclosure iff n exceeds a unique threshold
-- statement:
--   Fix the prior precision $q > 0$ and the prior mean $\bar\theta > 0$. The paper assumes that the disclosure cost $c_m$ is sufficiently large.
--
--   1. **No rollover risk.** For $a = 0$, every competition intensity $b \in (0, 1]$ and every private precision $n > 0$ have a cost bound $c_0$ such that for every $c_m \ge c_0$, the disclosure equilibrium with competition and the one without competition ($b = 0$) are both unique and symmetric, with the same precision:
--   $$m^* = m^{NC}.$$
--   2. **Rollover risk.** For every $a \in (0, \tfrac12)$ there is $c_0$ such that for every $c_m \ge c_0$ there is a threshold $\hat n > 0$ with the following property. For every $n > 0$, the disclosure equilibria at $b = 1$ and at $b = 0$ are unique and symmetric, $(m^*, m^*)$ and $(m^{NC}, m^{NC})$, and
--   $$m^* \le m^{NC} \text{ (strictly if } m^{NC} > 0) \iff n > \hat n.$$
--
--   This is the main result of the paper: competition between financial institutions makes them more opaque exactly when investors' private information is precise, and more transparent when it is imprecise.
--
--   **Formalization Note** The disclosure equilibrium is the Nash equilibrium of the FIs' choice of $m_i \ge 0$, with each FI's payoff (9) computed as an expectation under the model's Gaussian law with investors playing a linear equilibrium. In part 2 the bound $a < \tfrac12$ is added to the paper's $a > 0$, $a \le \tfrac12$: at $a = \tfrac12$, $b = 1$ a linear investor equilibrium fails for positive disclosure precisions. In part 2, $c_0$ is chosen before $n$, so $\hat n$ is a single threshold. In part 1, the cost bound is chosen for each $b$ and $n$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), pp. 17–18, Proposition 4; proof pp. 35–38

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- Proposition 4, pp. 17–18 (the main result). Fix the prior precision `q > 0` and the prior mean
`θ̄ > 0`. In part 1, "`c_m` sufficiently large" is quantified after each `b, n`. In part 2,
`∃ c₀, ∀ c_m ≥ c₀` is quantified before `n`, so the threshold is shared across `n`.
1. Without rollover risk (`a = 0`): for every competition intensity `b ∈ (0, 1]` and every
   `n > 0`, the disclosure equilibrium with competition and the one without (`b = 0`) are both
   unique, symmetric, and equal: `m* = mᴺᶜ`.
2. With rollover risk `a ∈ (0, 1/2)`: at `b = 1` and at `b = 0` the disclosure equilibria
   `(m*, m*)` and `(mᴺᶜ, mᴺᶜ)` are unique, and there is a threshold `n̂ > 0` such that, for every
   `n > 0`, `m* ≤ mᴺᶜ` (strictly if `mᴺᶜ > 0`) if and only if `n > n̂`.
The bound `a < 1/2` in part 2 is added: at `a = 1/2`, `b = 1` no linear investor equilibrium
exists at positive disclosure precisions. -/
theorem proposition_4 (q thetaBar : ℝ) (hq : 0 < q) (hθ : 0 < thetaBar) : (∀ b : ℝ, 0 < b → b ≤ 1 → ∀ n : ℝ, 0 < n → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ m₀ : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 b q n thetaBar cm m ↔ m = fun _ => m₀) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq 0 0 q n thetaBar cm m ↔ m = fun _ => m₀)) ∧ ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∃ nhat : ℝ, 0 < nhat ∧ ∀ n : ℝ, 0 < n → ∃ mS mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 1 q n thetaBar cm m ↔ m = fun _ => mS) ∧ (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ ((mS ≤ mNC ∧ (0 < mNC → mS < mNC)) ↔ nhat < n) := by sorry

end CompOpacity.Disclosure
