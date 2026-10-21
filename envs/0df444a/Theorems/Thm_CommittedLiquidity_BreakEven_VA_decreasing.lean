-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_VA_decreasing
-- name    : CommittedLiquidity.BreakEven.VA_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:24.795564+00:00
-- url     : https://prove2.me/theorems/c9d9fde7-e14d-4161-9c5c-5a70160602e1
-- title:
--   Proof of Proposition 3, p. 44 — regulator payoff decreases continuously
-- statement:
--   Under the standing assumptions, the regulator's expected payoff $V_A(P)$ from (22) is continuous on $[\underline P,qD_2]$ and strictly decreasing on $[\underline P,qD_2)$:
--
--   $$\underline P\le P<Q<qD_2\quad\Longrightarrow\quad V_A(Q)<V_A(P).$$
--
--   Together with the opposite endpoint signs, this gives existence and uniqueness of the regulator's break-even price.
--
--   **Formalization Note** The open upper endpoint is the paper's equilibrium-price domain. The closed endpoint is included only for continuity.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), p. 27 (PDF 28), continuity claim; App. B.5, p. 44 (PDF 45), derivative of V_A

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem VA_decreasing (p : Params) (hp : p.Standing) :
    ContinuousOn p.VA (Set.Icc p.Plow (p.q * p.D2)) ∧
      StrictAntiOn p.VA (Set.Ico p.Plow (p.q * p.D2)) := by sorry
end CommittedLiquidity.BreakEven
