-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_proposition_3
-- name    : CompOpacity.Disclosure.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:33.472846+00:00
-- url     : https://prove2.me/theorems/4ef1a309-97f6-49c8-9ada-8c1c572862f5
-- title:
--   Proposition 3, p. 15 (a > 0, m > 0, b ≤ 1 added) — unique linear equilibrium under competition; all four multipliers exceed 1
-- statement:
--   Let the competition intensity be $b \in (0, 1]$, the rollover risk $a \in (0, \tfrac12)$, $q, n, \bar\theta > 0$ and $m_1, m_2 > 0$. Write $\beta^{NC}_i = \dfrac{n}{q + m_i + (1-a)n}$ and $\gamma^{NC}_i = \dfrac{m_i}{(1-a)[q + m_i + (1-a)n]}$ for the no-competition coefficients of Lemma 1. Then the investors' game has a unique linear equilibrium
--   $$k^*_{ij} = \beta^*_i x_{ij} + \gamma^*_i z_i - b(\lambda^*_i x_{-ij} + \omega^*_i z_{-i}) + h^*_i,$$
--   and its multipliers
--   $$\kappa^*_i = \frac{\beta^*_i}{\beta^{NC}_i},\quad \nu^*_i = \frac{\gamma^*_i}{\gamma^{NC}_i},\quad \mu^*_i = \frac{\lambda^*_i}{\beta^{NC}_{-i}},\quad \chi^*_i = \frac{\omega^*_i}{\gamma^{NC}_{-i}}$$
--   all exceed $1$, while $h^*_i = \big(\gamma^*_i/m_i - b\,\omega^*_i/m_{-i}\big)q\bar\theta$.
--
--   This is the multiplier effect of competition: investors respond more strongly to every signal than without competition, which drives the comparison of disclosure choices in Proposition 4.
--
--   **Formalization Note** Four hypotheses are added to the page's "$b > 0$": $a > 0$ (at $a = 0$ all multipliers equal $1$ by (30)), $m_i, m_{-i} > 0$ (otherwise $\gamma^{NC} = 0$ and $\nu^*, \chi^*$ are undefined), and $a < \tfrac12$, $b \le 1$ (the fixed point exists only when $a(1+b) < 1$; the model has $b \in (0,1)$ and the limit $b = 1$).
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 15, Proposition 3; proof pp. 32–33, (25)–(30)

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- Proposition 3, p. 15 (with (29)–(30), pp. 32–33): with competition intensity `b ∈ (0, 1]`,
rollover risk `a ∈ (0, 1/2)` and positive disclosure precisions, there is a unique linear investor
equilibrium; writing `βᴺᶜᵢ = n/(q + mᵢ + (1 − a)n)`, `γᴺᶜᵢ = mᵢ/((1 − a)[q + mᵢ + (1 − a)n])`,
its multipliers `κᵢ = βᵢ/βᴺᶜᵢ`, `νᵢ = γᵢ/γᴺᶜᵢ`, `μᵢ = λᵢ/βᴺᶜ₋ᵢ`, `χᵢ = ωᵢ/γᴺᶜ₋ᵢ` all exceed `1`, and
`hᵢ = (γᵢ/mᵢ − bωᵢ/m₋ᵢ)qθ̄`.
Added hypotheses (not on the page): `a > 0` (at `a = 0` every multiplier equals `1` by (30));
`mᵢ, m₋ᵢ > 0` (otherwise `γᴺᶜ = 0` and `ν, χ` are undefined); `a < 1/2` and `b ≤ 1`
(existence of the fixed point needs `a(1 + b) < 1`). The `−i` terms of (25), (27)–(28) use
`x₋ᵢⱼ` (the page prints `xᵢⱼ`). -/
theorem proposition_3 (a b q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b ≤ 1) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hm : ∀ i, 0 < m i) : (∃! s : LinStrat, IsLinEq a b q n thetaBar m s) ∧ ∀ s : LinStrat, IsLinEq a b q n thetaBar m s → ∀ i : Fin 2, 1 < s.beta i / (n / (q + m i + (1 - a) * n)) ∧ 1 < s.gamma i / (m i / ((1 - a) * (q + m i + (1 - a) * n))) ∧ 1 < s.lam i / (n / (q + m i.rev + (1 - a) * n)) ∧ 1 < s.omega i / (m i.rev / ((1 - a) * (q + m i.rev + (1 - a) * n))) ∧ s.h i = (s.gamma i / m i - b * s.omega i / m i.rev) * q * thetaBar := by sorry

end CompOpacity.Disclosure
