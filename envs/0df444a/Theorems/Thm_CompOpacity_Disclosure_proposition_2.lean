-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_proposition_2
-- name    : CompOpacity.Disclosure.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:41.589034+00:00
-- url     : https://prove2.me/theorems/d9154eff-e4ca-44db-99f5-4fe70ee2b7c1
-- title:
--   Proposition 2, p. 14 — without competition, m^NC > 0 solves the FOC iff a > 5/8 − (1/8)√(16q/n + 9); otherwise m^NC = 0
-- statement:
--   Without competition ($b = 0$), let $a \in [0, \tfrac12]$ and $q, \bar\theta > 0$. There is $c_0$ such that for every disclosure cost $c_m \ge c_0$ and every private precision $n > 0$ the disclosure equilibrium is unique and symmetric, $(m^{NC}, m^{NC})$, and:
--   1. if $a > \tfrac58 - \tfrac18\sqrt{16q/n + 9}$, then $m^{NC} > 0$ and it solves the first-order condition
--   $$\frac{m^{NC} + q - (1-a)(1-4a)n}{2(1-a)^2[q + m^{NC} + (1-a)n]^3} - c_m m^{NC} = 0;$$
--   2. if $a \le \tfrac58 - \tfrac18\sqrt{16q/n + 9}$, then $m^{NC} = 0$.
--
--   This is the no-competition benchmark against which Proposition 4 measures the effect of competition.
--
--   **Formalization Note** The paper's standing assumption that $c_m$ is "sufficiently large" (p. 8) is encoded as $\exists c_0\, \forall c_m \ge c_0$, with $c_0$ chosen before $n$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 14, Proposition 2; proof pp. 33–35

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- Proposition 2, p. 14: without competition (`b = 0`), for `c_m` sufficiently large (one bound
`c₀` for all `n > 0`), the disclosure equilibrium is unique and symmetric, `m = (mᴺᶜ, mᴺᶜ)`; if
`a > 5/8 − (1/8)√(16q/n + 9)` then `mᴺᶜ > 0` solves the first-order condition `∂Πᴺᶜ/∂m = 0`
of (33), and if `a ≤ 5/8 − (1/8)√(16q/n + 9)` then `mᴺᶜ = 0`. -/
theorem proposition_2 (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n : ℝ, 0 < n → ∃ mNC : ℝ, (∀ m : Fin 2 → ℝ, IsDisclosureEq a 0 q n thetaBar cm m ↔ m = fun _ => mNC) ∧ (5 / 8 - Real.sqrt (16 * q / n + 9) / 8 < a → 0 < mNC ∧ margNC a q n mNC - cm * mNC = 0) ∧ (a ≤ 5 / 8 - Real.sqrt (16 * q / n + 9) / 8 → mNC = 0) := by sorry

end CompOpacity.Disclosure
