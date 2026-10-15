-- Prove2me | Theorems.Thm_DigitalPrivacy_Strategy_appA2_three_regimes
-- name    : DigitalPrivacy.Strategy.appA2_three_regimes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:40.972584+00:00
-- url     : https://prove2.me/theorems/4847d4d3-e8bb-43df-b60f-95364f3e545a
-- title:
--   App. A.2, p. 31 — three regimes: ξ* = 1 for ψ ≤ ψ_L, interior ξ_i for ψ_L < ψ < ψ_H, no collection for ψ ≥ ψ_H
-- statement:
--   Let $0 \le \beta < 1$, $0 < \rho < 1$, $\psi > 0$ and $0 < P \le 1$. Define the thresholds
--   $$\psi_L = \frac{(P+\rho+P\rho)^2}{4(1+\rho)}, \qquad \psi_H = \frac{(P+(1-P)\rho)^2}{4(1-P)} \quad (\psi_H = +\infty \text{ if } P = 1),$$
--   the interior root $\xi_i = \frac{1}{2P\rho}\big(-(1-P)\rho - P + |P-(1-P)\rho|\sqrt{\psi/(\psi-P\rho)}\big)$, and $C_h$ as in Lemma 1. Then $P\rho \le \psi_L \le \psi_H$, and:
--
--   1. if $\psi \le \psi_L$, then $(\xi, C) = (1, C_h(1))$ is a business optimum;
--   2. if $\psi_L < \psi < \psi_H$, then $\xi_i \in (0, 1)$ and $(\xi_i, C_h(\xi_i))$ is a business optimum;
--   3. if $\psi \ge \psi_H$, then $(0, 0)$ is a business optimum.
--
--   Here a business optimum is a strategy $(\xi, C) \in [0,1] \times [0, \infty)$ maximizing the profit $\Pi$ over $[0,1] \times [0,\infty)$. This is the case analysis from which the closed form (5)–(6) of Theorem 1 is read off.
--
--   **Formalization Note** The page writes $P\rho < \psi_L \le \psi_H$; the strict inequality fails at $P = \rho/(1+\rho)$, where $\psi_L = \psi_H = P\rho$, so the non-strict form is stated. Each case asserts "a" business optimum, not "the": at $P = \rho/(1+\rho)$, $\psi = \rho^2/(1+\rho)$, cases 1 and 3 both apply and $(1, C_h(1))$ and $(0,0)$ give the same profit. $\psi \ge \psi_H$ is written $(P+(1-P)\rho)^2 \le 4(1-P)\psi$ and $\psi < \psi_H$ as the strict reverse, so that $P = 1$ needs no division by zero; $\psi_L \le \psi_H$ is stated for $P < 1$ in the same multiplied-out form. The assumptions $\psi > 0$, $\rho > 0$, $P > 0$ are added to the page's ranges because $\xi_i$ divides by $2P\rho$ and $C_h$ by $\psi$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 31, App. A.2, summary paragraph (with ψ_L, ψ_H and ξ_i from p. 30)

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

namespace DigitalPrivacy.Strategy

/-- App. A.2, summary paragraph, p. 31: the thresholds satisfy `Pρ ≤ ψ_L ≤ ψ_H` (with
`ψ_H = (P + (1−P)ρ)²/(4(1−P))`, `ψ_H = +∞` at `P = 1`), and (i) if `ψ ≤ ψ_L` then
`(1, C_h(1))` is a business optimum; (ii) if `ψ_L < ψ < ψ_H` then `ξ_i ∈ (0, 1)` and
`(ξ_i, C_h(ξ_i))` is a business optimum; (iii) if `ψ ≥ ψ_H` then `(0, 0)` is a business optimum. -/
theorem appA2_three_regimes (β ρ ψ P : ℝ) (hS : Standing β ρ ψ P) :
    P * ρ ≤ psiL ρ P ∧
    (P < 1 → 4 * (1 - P) * psiL ρ P ≤ (P + (1 - P) * ρ) ^ 2) ∧
    (ψ ≤ psiL ρ P → IsBusinessOpt β ρ ψ P 1 (Ch β ρ ψ P 1)) ∧
    (psiL ρ P < ψ → 4 * (1 - P) * ψ < (P + (1 - P) * ρ) ^ 2 →
      0 < xiI ρ ψ P ∧ xiI ρ ψ P < 1 ∧
      IsBusinessOpt β ρ ψ P (xiI ρ ψ P) (Ch β ρ ψ P (xiI ρ ψ P))) ∧
    ((P + (1 - P) * ρ) ^ 2 ≤ 4 * (1 - P) * ψ → IsBusinessOpt β ρ ψ P 0 0) := by sorry

end DigitalPrivacy.Strategy
