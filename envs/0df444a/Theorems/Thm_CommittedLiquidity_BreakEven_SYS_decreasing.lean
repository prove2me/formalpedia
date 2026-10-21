-- Prove2me | Theorems.Thm_CommittedLiquidity_BreakEven_SYS_decreasing
-- name    : CommittedLiquidity.BreakEven.SYS_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:53.74098+00:00
-- url     : https://prove2.me/theorems/b480ceaf-5407-482a-ac0f-22771bb40e64
-- title:
--   Proof of Proposition 3, p. 45 — systemic-failure risk decreases with support price
-- statement:
--   Under the standing assumptions, the probability of systemic bank failures under a committed price $P$ is strictly decreasing on the valid price interval:
--
--   $$\underline P\le P<Q<qD_2\quad\Longrightarrow\quad \mathrm{SYS}(Q)<\mathrm{SYS}(P).$$
--
--   A higher support price lowers the critical cash flow and therefore lowers the probability that both banks fail.
--
--   **Formalization Note** $\mathrm{SYS}(P)$ uses the limiting threshold $\theta^*(P)$ in the uniform closed form on p. 26.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), App. B.5, p. 45 (PDF 46), derivative of SYS

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

namespace CommittedLiquidity.BreakEven

theorem SYS_decreasing (p : Params) (hp : p.Standing) :
    StrictAntiOn p.SYS (Set.Ico p.Plow (p.q * p.D2)) := by sorry
end CommittedLiquidity.BreakEven
