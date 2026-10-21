-- Prove2me | Theorems.Thm_FollowCustomers_SmallCost_thresholds_tendsto_half
-- name    : FollowCustomers.SmallCost.thresholds_tendsto_half
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:48.801837+00:00
-- url     : https://prove2.me/theorems/11fc839a-410c-4896-af26-80369dbf7d02
-- title:
--   §3.4, p. 14 (PDF 16) — on every solution branch, x̲, x* → 1/2 as K → 0
-- statement:
--   Let $r,\sigma^2,\delta>0$, and let $K\mapsto(\underline x(K),x^*(K))$ be a solution branch of (14)–(15): for every sufficiently small $K>0$ the pair solves (14)–(15) in the region $\tfrac12<\underline x<x^*<1$, $\delta(2x^*-1)<3$. Then
--   $$\lim_{K\to0^+}x^*(K)=\tfrac12,\qquad \lim_{K\to0^+}\underline x(K)=\tfrac12 .$$
--
--   When repositioning is free, a firm moves at once to the side of the market closer to the consumers, so both thresholds collapse to the midpoint. In the appendix this is obtained from (xii), which gives $G\to1$ and hence $\underline p=p^*$ in the limit, and (xiv), $\underline p^2+p^{*2}=2$, which gives $\underline p,p^*\to1$.
--
--   **Formalization Note.** The limit is along $K\to0^+$ (`𝓝[>] 0`). No continuity of the branch is assumed.
-- source:
--   Ning & Villas-Boas, Following the Customers: Dynamic Competitive Repositioning, SSRN 3695318 (December 2020), §3.4, p. 14 (PDF 16); Appendix p. 30 (PDF 32), (xiv)

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

namespace FollowCustomers.SmallCost

/-- On every solution branch, `x̲, x* → 1/2` as `K → 0⁺` (p. 14; (xiv), p. 30). -/
theorem thresholds_tendsto_half (P : Params) (xl xs : ℝ → ℝ) (hP : P.Standing)
    (hb : IsBranch P xl xs) :
    Tendsto xs (𝓝[>] 0) (𝓝 (1 / 2)) ∧ Tendsto xl (𝓝[>] 0) (𝓝 (1 / 2)) := by sorry

end FollowCustomers.SmallCost
