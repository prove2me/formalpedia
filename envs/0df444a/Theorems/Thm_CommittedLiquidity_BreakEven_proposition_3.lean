-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_proposition_3
-- name    : CommittedLiquidity.BreakEven.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:54.280986+00:00
-- url     : https://prove2.me/theorems/edcafbcd-d101-42d5-bea4-2779c3ba3b42
-- title:
--   Proposition 3, p. 26 — unique break-even committed price minimizes systemic risk
-- statement:
--   Consider the paper's two-bank model in the $\epsilon,\eta\to0$ regime under its standing assumptions, and let $P_1^*$ and $P_2^*$ be the buyers' break-even prices after one and two observed runs. The systemic-failure probability $\mathrm{SYS}(P)$ and the regulator's expected payoff $V_A(P)$ are strictly decreasing on $[\underline P,qD_2)$. There is a unique price $P_A^*$ between the market prices at which the regulator breaks even:
--
--   $$P_2^*<P_A^*<P_1^*,\qquad V_A(P_A^*)=0.$$
--
--   This price is feasible and minimizes $\mathrm{SYS}(P)$ over all $P\ge P_2^*$ satisfying $V_A(P)\ge0$ and $\theta^*(P)\ge D_2$, the regulator's program (20)–(21). It strictly reduces systemic-failure risk relative to the two-run market price:
--
--   $$\mathrm{SYS}(P_A^*)<\mathrm{SYS}(P_2^*).$$
--
--   The result identifies a committed liquidity-support price that pays for itself in expectation while lowering systemic bank failures.
--
--   **Formalization Note** The statement uses the closed forms for the $\epsilon,\eta\to0$ limit, including $V_A$ from (22). The paper prints $\mathrm{SYS}(\theta_2^*)$ in its final comparison; in the limit $\theta_2^*=\theta^*(P_2^*)$, which is the benchmark stated here. Uniqueness ranges over all zeros in $(P_2^*,P_1^*)$.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 26 (PDF 27), Proposition 3; p. 25 (PDF 26), program (20)–(21); App. B.5, pp. 44–45 (PDF 45–46)

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem proposition_3 (p : Params) (hp : p.Standing) (P1 P2 : ℝ)
    (hP1 : p.IsBreakEven 1 P1) (hP2 : p.IsBreakEven 2 P2) :
    StrictAntiOn p.SYS (Set.Ico p.Plow (p.q * p.D2)) ∧
    StrictAntiOn p.VA (Set.Ico p.Plow (p.q * p.D2)) ∧
    ∃ PA, (PA ∈ Set.Ioo P2 P1 ∧ p.VA PA = 0) ∧
      (∀ P, P ∈ Set.Ioo P2 P1 → p.VA P = 0 → P = PA) ∧
      PA ∈ {P | P2 ≤ P ∧ 0 ≤ p.VA P ∧ p.D2 ≤ p.θstar P} ∧
      IsMinOn p.SYS {P | P2 ≤ P ∧ 0 ≤ p.VA P ∧ p.D2 ≤ p.θstar P} PA ∧
      p.sysOfTheta (p.θstar PA) < p.sysOfTheta (p.θstar P2) := by sorry
end CommittedLiquidity.BreakEven
