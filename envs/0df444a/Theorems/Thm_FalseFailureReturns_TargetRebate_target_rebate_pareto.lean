-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_target_rebate_pareto
-- name    : FalseFailureReturns.TargetRebate.target_rebate_pareto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:45:28.335035+00:00
-- url     : https://prove2.me/theorems/7db73960-5afe-46df-b3c6-a5a87a2e4b92
-- title:
--   Proposition 2 — a coordinating target rebate helps the retailer, and the manufacturer iff $\rho^C \ge 2\rho^D$
-- statement:
--   Consider one manufacturer and one retailer. Let $a > 0$ be the marginal effort cost, $\beta > 0$ the expected number of false failures at the minimum effort level, and $M_m = m + \delta_m(w - c) > 0$, $R_r = r + \delta_r(p - w) > 0$ the manufacturer's and the retailer's profits of avoiding one false failure return, in the interesting case $(M_m + R_r)\beta > a$. Suppose that at effort $\rho$ the number of false failures is $X(\rho) \sim \mathrm{Uniform}(0, 2\beta/\rho)$. Write
--   $$\rho^C = \Big[\frac{M_m + R_r}{a}\,\beta\Big]^{1/3}, \qquad \rho^D = \max\Big\{\Big(\frac{R_r\beta}{a}\Big)^{1/3},\,1\Big\}$$
--   for the coordinated and the decentralized effort.
--
--   Let $(u, T)$ be a target rebate contract (the retailer receives $u$ for every false failure below the target $T$) with $u > 0$, $T > 0$ and $T < 2\beta/\rho^C$, which coordinates the supply chain: $\rho^C$ maximizes the retailer's expected profit $\pi_R(\rho \mid T, u)$ of Eq. (6) over efforts $\rho \ge 1$. Then
--
--   1. the contract makes the retailer better off: $$\pi_R(\rho^C \mid T, u) \ge \pi_R(\rho^D);$$
--   2. the contract makes the manufacturer better off if and only if the coordinated effort is at least twice the decentralized effort: $$\pi_M(\rho^C \mid T, u) \ge \pi_M(\rho^D) \iff \rho^C \ge 2\rho^D.$$
--
--   Here $\pi_R(\rho^D)$ and $\pi_M(\rho^D)$ are the no-contract profits (3) and (5), and $\pi_M(\rho \mid T, u)$ is the manufacturer's profit (7) under the contract. The result says that a coordinating target rebate is a Pareto improvement over no contract exactly when the retailer's own incentive to exert effort is weak relative to the supply chain's.
--
--   **Formalization Note** The paper's interesting case is printed as $(m + r)\beta > a$; the condition equivalent to $\rho^C > 1$, which the proof uses, is $(M_m + R_r)\beta > a$, and that is the hypothesis here. The side condition $T < 2\beta/\rho^C$ is the paper's §3.1 requirement $T < 2\beta/\rho$ at the coordinated effort. The expectation in (6)–(7) is the true uniform expectation for every effort.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 383, Proposition 2 (proof: Appendix, pp. 392–393)

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model
import Definitions.Def_FalseFailureReturns_TargetRebate_UniformRebate

namespace FalseFailureReturns.TargetRebate

theorem target_rebate_pareto (P : Params) (T u : ℝ)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) (hu : 0 < u) (hT : 0 < T)
    (hTlt : T < 2 * P.β / coordEffort P) (hcoord : Coordinates P T u) :
    retailerProfit P (decentrEffort P) ≤ rebateRetailerProfit P T u (coordEffort P) ∧
      (manufProfit P (decentrEffort P) ≤ rebateManufProfit P T u (coordEffort P) ↔
        2 * decentrEffort P ≤ coordEffort P) := by sorry

end FalseFailureReturns.TargetRebate
