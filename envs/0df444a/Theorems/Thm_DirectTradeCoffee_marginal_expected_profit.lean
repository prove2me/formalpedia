-- Prove2me | Theorems.Thm_DirectTradeCoffee_marginal_expected_profit
-- name    : DirectTradeCoffee.marginal_expected_profit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:27.482419+00:00
-- url     : https://prove2.me/theorems/b62421f5-311a-45a0-839d-3a2cb23e3e58
-- title:
--   Proof of Proposition 2, p.43, display $\Pi'(Q)=\mu_\varphi+\rho\sigma_\varphi\sigma_y+\lambda(Q)-k'(Q)-c$ — the marginal expected profit
-- statement:
--   At every $Q>0$ the function $\Pi+k$ is differentiable, with
--
--   $$
--   (\Pi+k)'(Q) = \mu_\varphi + \rho\sigma_\varphi\sigma_y + \lambda(Q) - c .
--   $$
--
--   Equivalently, wherever $k$ is differentiable, $\Pi'(Q) = \mu_\varphi + \rho\sigma_\varphi\sigma_y + \lambda(Q) - k'(Q) - c$, and in general the right (left) derivative of $\Pi$ is given by this formula with the right (left) derivative of $k$. The term $\mu_\varphi+\rho\sigma_\varphi\sigma_y$ is the revenue of a marginal acre sold as blend, and $\lambda(Q)$ is the expected second-stage shadow price of supply.
--
--   Differences from the source:
--   - generalization: Π′(Q) = μ_φ + ρσ_φσ_y + λ(Q) − k′(Q) − c, with k′ the right derivative where one-sided derivatives differ (p.13) → HasDerivAt of Π + k with value μ_φ + ρσ_φσ_y + λ(Q) − c; reason: k need not be differentiable; subtracting the right or left derivative of k gives the printed display on either side
--   - encoding: the display for all Q ≥ 0 → Q > 0; reason: at Q = 0 the right derivative of Π is +∞, so the display has no real value there
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - reading: p.13 illustrates a capacity limit Q_max by k′(Q_max) = ∞ → k is real-valued and continuous on [0, ∞), as p.10 and p.31 assume; reason: the illustration lies outside the model assumption that k is a continuous function; every k of the model is covered
--   - encoding: second-stage constraint 0 ≤ q ≤ 1 → 0 ≤ q < 1; reason: at q = 1 no finite price clears the market and the objective tends to −∞; the maximum and its maximizer are unchanged
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
--   - encoding: μ_φ + ρσ_φσ_y → U.meanφ + U.cov, with the covariance ∫(φ − μ_φ)(y − 1) dF; reason: ρ is undefined when a variance is 0; the two agree whenever ρ is defined
--   - encoding: λ(Q) = E[(m_c − m_u)⁺] → the integrand is written as 0 where Qy ≥ 1; reason: the paper sets the positive part to 0 at every unconstrained realization, p.13, and m_c, m_u are undefined for Qy ≥ 1; the value is the same at every realization
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, proof of Proposition 2, pp.42–43, display Π′(Q) = μ_φ + ρσ_φσ_y + λ(Q) − k′(Q) − c, p.43

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **Marginal expected profit**, Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for
Specialty Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, proof of Proposition 2, p.43, display
`Π′(Q) = μ_φ + ρσ_φσ_y + λ(Q) − k′(Q) − c`.

**Formalization Note.** `k` need not be differentiable, so the identity is stated for `Π + k`, which
is differentiable at every `Q > 0` with derivative `μ_φ + ρσ_φσ_y + λ(Q) − c`. The printed display
with the right (left) derivative of `k` follows by subtracting `k′₊` (`k′₋`). `Q = 0` is excluded:
the right derivative there is `+∞`. -/
theorem marginal_expected_profit (P : Params) {k : ℝ → ℝ} (hk : IsCost k) (U : Uncertainty)
    (Q : ℝ) (hQ : 0 < Q) :
    HasDerivAt (fun R => expectedProfit P k U R + k R) (U.meanφ + U.cov + lam P U Q - P.c) Q := by sorry

end DirectTradeCoffee
