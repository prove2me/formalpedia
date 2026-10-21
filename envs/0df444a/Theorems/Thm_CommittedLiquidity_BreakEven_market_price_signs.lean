-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_market_price_signs
-- name    : CommittedLiquidity.BreakEven.market_price_signs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:40.048717+00:00
-- url     : https://prove2.me/theorems/592ccf40-8693-4e9c-bcab-643fb3ec3da2
-- title:
--   §3.3, p. 27 — opposite regulator-payoff signs at the market prices
-- statement:
--   Let $P_1^*$ and $P_2^*$ be the break-even asset prices after one and two runs. Under the standing assumptions,
--
--   $$\Pi_1(P_2^*)>0,\qquad \Pi_2(P_1^*)<0,\qquad V_A(P_2^*)>0,\qquad V_A(P_1^*)<0.$$
--
--   The regulator earns a surplus at the lower market price and incurs a loss at the higher one. These signs locate the regulator's break-even price between them.
--
--   **Formalization Note** Both prices satisfy the paper's break-even condition and belong to $[\underline P,qD_2)$.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 27 (PDF 28), §3.3, paragraph following equation (23)

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem market_price_signs (p : Params) (hp : p.Standing) (P1 P2 : ℝ)
    (hP1 : p.IsBreakEven 1 P1) (hP2 : p.IsBreakEven 2 P2) :
    0 < p.Pi 1 P2 ∧ p.Pi 2 P1 < 0 ∧ 0 < p.VA P2 ∧ p.VA P1 < 0 := by sorry
end CommittedLiquidity.BreakEven
