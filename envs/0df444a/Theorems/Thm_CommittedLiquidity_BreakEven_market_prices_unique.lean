-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_market_prices_unique
-- name    : CommittedLiquidity.BreakEven.market_prices_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:29.720746+00:00
-- url     : https://prove2.me/theorems/1eb4739f-930c-444e-97c1-e06367870a31
-- title:
--   §3.3, p. 27 — the two market break-even prices exist uniquely
-- statement:
--   For each number of bank runs $M\in\{1,2\}$, let $\Pi_M(P)$ be the buyers' expected profit at price $P$ when their posterior is conditioned on observing $M$ runs. Under the standing assumptions, $\Pi_M$ is strictly decreasing on $[\underline P,qD_2]$. There is exactly one price $P_M^*$ in $[\underline P,qD_2)$ with
--
--   $$\Pi_M(P_M^*)=0.$$
--
--   These prices are the market benchmarks for the regulator's policy.
--
--   **Formalization Note** The statement uses the paper's limiting cash-flow threshold $\theta^*(P)$. The market-price range is included in the definition of a break-even price.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 27 (PDF 28), §3.3, paragraph defining Π_M; App. B.3, p. 40 (PDF 41), Step 1

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem market_prices_unique (p : Params) (hp : p.Standing) :
    ∀ M ∈ ({1, 2} : Finset ℕ),
      StrictAntiOn (p.Pi M) (Set.Icc p.Plow (p.q * p.D2)) ∧
      ∃! P, p.IsBreakEven M P := by sorry
end CommittedLiquidity.BreakEven
