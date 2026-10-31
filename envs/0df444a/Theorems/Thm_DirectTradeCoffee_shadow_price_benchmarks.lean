-- Prove2me | Theorems.Thm_DirectTradeCoffee_shadow_price_benchmarks
-- name    : DirectTradeCoffee.shadow_price_benchmarks
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:35.230532+00:00
-- url     : https://prove2.me/theorems/09ec62fd-dba6-4abd-a988-e935cc4b3177
-- title:
--   §4.2, text after Proposition 3, p.15 — $\lambda(Q)=0$ iff $Q\ge Q_H$; $m_c-m_u>0$ everywhere iff $Q<Q_L$; $\lambda=\bar m_c-\bar m_u$ iff $Q\le Q_L$
-- statement:
--   The expected shadow price behaves as follows at the benchmarks.
--
--   1. For $Q>0$: $\lambda(Q)=0$ if and only if $Q\ge Q_H$.
--   2. For $0<Q<1/y_h$: $m_c(Q,\varphi,y)-m_u(Q,y)>0$ at every realization $(\varphi,y)\in\Omega$ if and only if $Q<Q_L$.
--   3. For $0<Q<1/y_h$: $\lambda(Q)=\bar m_c(Q)-\bar m_u(Q)$ if and only if $Q\le Q_L$.
--
--   These facts turn the marginal revenue $\mu_\varphi+\rho\sigma_\varphi\sigma_y+\lambda(Q)$ into the two simple forms that appear in the optimality conditions of specialized and diversified sourcing.
--
--   Differences from the source:
--   - encoding: claims 2 and 3 for Q with no stated range → 0 < Q and Q y_h < 1; reason: this is exactly 0 < Qy < 1 on Ω, outside which m_c and m_u are undefined; Q_L < 1/y_h always
--   - encoding: for every realization of (φ̃, ỹ) → for every point of Ω; reason: Ω is the support
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
--   - encoding: λ(Q) = E[(m_c − m_u)⁺] → the integrand is written as 0 where Qy ≥ 1; reason: the paper sets the positive part to 0 at every unconstrained realization, p.13, and m_c, m_u are undefined for Qy ≥ 1; the value is the same at every realization
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, §4.2, text after Proposition 3, p.15

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **The shadow price at the benchmarks**, Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies
for Specialty Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, §4.2, text after Proposition 3, p.15.

For `Q > 0`, `λ(Q) = 0` iff `Q ≥ Q_H`. For `0 < Q < 1/y_h`, `m_c − m_u > 0` at every realization of
`Ω` iff `Q < Q_L`, and `λ(Q) = m̄_c(Q) − m̄_u(Q)` iff `Q ≤ Q_L`.

**Formalization Note.** `0 < Q < 1/y_h` means `0 < Qy < 1` on all of `Ω`, the range in which `m_c`
and `m_u` are defined. It is not a restriction of the claims: outside it the formulas are undefined
in the paper, and `Q_L < 1/y_h` always. -/
theorem shadow_price_benchmarks (P : Params) (U : Uncertainty) :
    (∀ Q, 0 < Q → (lam P U Q = 0 ↔ QH P U ≤ Q)) ∧
    (∀ Q, 0 < Q → Q * U.yh < 1 →
      ((∀ z ∈ U.Ω, 0 < mc P Q z.1 z.2 - mu P Q z.2) ↔ Q < QL P U)) ∧
    (∀ Q, 0 < Q → Q * U.yh < 1 → (lam P U Q = mcBar P U Q - muBar P U Q ↔ Q ≤ QL P U)) := by sorry

end DirectTradeCoffee
