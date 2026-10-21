-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_mNC_antitone
-- name    : CompOpacity.Disclosure.mNC_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:35.986682+00:00
-- url     : https://prove2.me/theorems/64b230f7-b952-42f1-b88a-cbd940502b9e
-- title:
--   Proof of Proposition 2, p. 35 — the no-competition disclosure precision m^NC is decreasing in n
-- statement:
--   Without competition ($b = 0$), let $a \in [0, \tfrac12]$ and $q, \bar\theta > 0$. There is $c_0$ such that for every $c_m \ge c_0$: if $0 < n_1 \le n_2$ and $(m_1, m_1)$, $(m_2, m_2)$ are disclosure equilibria at private precisions $n_1$ and $n_2$ respectively, then
--   $$m_2 \le m_1, \qquad\text{and}\qquad m_2 < m_1 \text{ if moreover } n_1 < n_2 \text{ and } m_1 > 0.$$
--
--   More precise private information crowds out public disclosure. The proof of Proposition 4 uses this monotonicity to turn the sign condition on $L(n/(q + m^{NC}))$ into a single threshold on $n$.
--
--   **Formalization Note** The page shows strict decrease where $m^{NC} > 0$ and $m^{NC} = 0$ beyond $n \ge q/((1-a)(1-4a))$; the statement is the resulting weak monotonicity together with the strict decrease at an interior $m^{NC}$ ($\partial m^{NC}/\partial n < 0$, p. 35). "$c_m$ sufficiently large" is $\exists c_0\, \forall c_m \ge c_0$, uniform in $n$.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 35, proof of Proposition 2

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- Proof of Proposition 2, p. 35: for `c_m` sufficiently large, the no-competition disclosure
precision `mᴺᶜ` is decreasing in the private-information precision `n`: if
`(m₁, m₁)` is a disclosure equilibrium at `n₁` and `(m₂, m₂)` one at `n₂ ≥ n₁`, then
`m₂ ≤ m₁`, and strictly where the precision is interior (p. 35, `∂mᴺᶜ/∂n < 0` at an interior
`mᴺᶜ`): if moreover `n₁ < n₂` and `m₁ > 0`, then `m₂ < m₁`. -/
theorem mNC_antitone (a q thetaBar : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hθ : 0 < thetaBar) : ∃ c₀ : ℝ, ∀ cm : ℝ, c₀ ≤ cm → ∀ n₁ n₂ m₁ m₂ : ℝ, 0 < n₁ → n₁ ≤ n₂ → IsDisclosureEq a 0 q n₁ thetaBar cm (fun _ => m₁) → IsDisclosureEq a 0 q n₂ thetaBar cm (fun _ => m₂) → m₂ ≤ m₁ ∧ (n₁ < n₂ → 0 < m₁ → m₂ < m₁) := by sorry

end CompOpacity.Disclosure
