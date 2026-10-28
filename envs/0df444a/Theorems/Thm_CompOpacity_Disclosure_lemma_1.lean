-- Prove2me | Theorems.Thm_CompOpacity_Disclosure_lemma_1
-- name    : CompOpacity.Disclosure.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:38.300172+00:00
-- url     : https://prove2.me/theorems/f72b1f0e-e5f8-49ab-84f3-486c882401ae
-- title:
--   Lemma 1, p. 11 — at b = 0 the linear investor equilibria are exactly β = n/(q+m+(1−a)n), γ = m/((1−a)[q+m+(1−a)n]), h = qθ̄/((1−a)[q+m+(1−a)n])
-- statement:
--   Consider the model without competition, $b = 0$, with rollover risk $a \in [0, \tfrac12]$, prior precision $q > 0$, private precision $n > 0$, prior mean $\bar\theta > 0$ and disclosure precisions $m_1, m_2 \ge 0$. A linear strategy $k_{ij} = \beta_i x_{ij} + \gamma_i z_i + h_i$ (the competition terms are multiplied by $b = 0$) is an equilibrium of the investors' game if and only if, for each FI $i$,
--   $$\beta_i = \frac{n}{q + m_i + (1-a)n}, \qquad \gamma_i = \frac{m_i}{(1-a)[q + m_i + (1-a)n]}, \qquad h_i = \frac{q\bar\theta}{(1-a)[q + m_i + (1-a)n]}.$$
--
--   This is the investment benchmark of the paper: investors place relative weight $m_i/((1-a)n)$ on the public report, more than its relative precision $m_i/n$, and the FI's no-competition disclosure problem is solved against these coefficients.
--
--   **Formalization Note** Uniqueness is within linear strategies; the paper's footnote 10 claims uniqueness among all equilibria, which is not formalized. The coefficients $\lambda_i, \omega_i$ of a linear strategy multiply $b = 0$ and are left unconstrained.
-- source:
--   Zhang, Competition and Opacity in the Financial System, SSRN 3428683 (2019-09-07 posting), p. 11, Lemma 1; proof p. 32, (25)–(28)

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

namespace CompOpacity.Disclosure

/-- Lemma 1, p. 11 (with (25)–(28), p. 32): absent competition (`b = 0`), the linear investor
equilibria are exactly the strategies with
`βᵢ = n/(q + mᵢ + (1 − a)n)`, `γᵢ = mᵢ/((1 − a)[q + mᵢ + (1 − a)n])` and
`hᵢ = qθ̄/((1 − a)[q + mᵢ + (1 − a)n])` for both FIs. At `b = 0` the coefficients `λᵢ, ωᵢ` are
multiplied by `0` in (25)–(28) and are left unconstrained. Only uniqueness within linear strategies
is stated (footnote 10's uniqueness among all equilibria is not formalized). The `−i` posterior in
(27)–(28) uses `x₋ᵢⱼ` (the page prints `xᵢⱼ`). -/
theorem lemma_1 (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hm : ∀ i, 0 ≤ m i) (s : LinStrat) : IsLinEq a 0 q n thetaBar m s ↔ ∀ i : Fin 2, s.beta i = n / (q + m i + (1 - a) * n) ∧ s.gamma i = m i / ((1 - a) * (q + m i + (1 - a) * n)) ∧ s.h i = q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n)) := by sorry

end CompOpacity.Disclosure
