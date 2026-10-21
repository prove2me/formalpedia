-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_lemma_3_price_order
-- name    : CommittedLiquidity.BreakEven.lemma_3_price_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.461041+00:00
-- url     : https://prove2.me/theorems/9e5e5478-c266-47f8-b340-a218975e1b26
-- title:
--   Lemma 3, p. 19 — the one-run market price exceeds the two-run price
-- statement:
--   Let $P_1^*$ and $P_2^*$ be buyers' break-even prices for one and two observed bank runs, respectively, under the standing assumptions. In the limiting regime,
--
--   $$P_2^*<P_1^*,\qquad \theta^*(P_1^*)<\theta^*(P_2^*).$$
--
--   More observed runs lead to a lower market price and a higher critical cash flow. This is the price and cash-flow ordering used by Proposition 3.
--
--   **Formalization Note** This is the price and critical-cash-flow part of Lemma 3 after $\epsilon,\eta\to0$. The creditor-signal and strategy assertions of the global game are outside this mission.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 19 (PDF 20), Lemma 3 and system (18); p. 22 (PDF 23), limiting Assumption

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem lemma_3_price_order (p : Params) (hp : p.Standing) (P1 P2 : ℝ)
    (hP1 : p.IsBreakEven 1 P1) (hP2 : p.IsBreakEven 2 P2) :
    P2 < P1 ∧ p.θstar P1 < p.θstar P2 := by sorry
end CommittedLiquidity.BreakEven
