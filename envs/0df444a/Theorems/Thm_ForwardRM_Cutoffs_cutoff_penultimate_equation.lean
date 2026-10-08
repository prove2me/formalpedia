-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_cutoff_penultimate_equation
-- name    : ForwardRM.Cutoffs.cutoff_penultimate_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:59:46.564593+00:00
-- url     : https://prove2.me/theorems/d99ae70a-4f53-45d5-98e2-00059ba7c625
-- title:
--   (4.7) — m(x^k_{T−1}) = δ E_T[max{m(x^k_{T−1}), m(v^k_T)}]
-- statement:
--   Suppose demand $N_t$ is weakly decreasing in the usual stochastic order, $T\ge 2$ and $k\ge1$. In period $T-1$ the seller balances the revenue from allocating the $k$-th good against the opportunity cost of denying it to the $k$-th highest new entrant: the cutoff $x^k_{T-1}$ solves
--
--   $$
--   m(x^k_{T-1})=\delta\,E_T\Big[\max\{m(x^k_{T-1}),\,m(v^k_T)\}\Big],
--   $$
--
--   where $v^k_T$ is the $k$-th highest value among the period-$T$ entrants. If fewer than $k$ buyers enter in period $T$, the maximum is $m(x^k_{T-1})$.
--
--   Together with $m(x^k_T)=0$, this is the start of the backward recursion of difference equations (4.6)–(4.8) for the cutoffs.
--
--   **Formalization Note** $E_T[\max\{a,X\}]$ is written as $a+E_T[(X-a)^+]$. The missing-entrant convention is the reading of footnote 15 ("entries equal zero") as "no buyer".
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 18, §4.2, eq. (4.7)

import Mathlib
import Definitions.Def_ForwardRM_Cutoffs_Model
import Definitions.Def_ForwardRM_Cutoffs_ValueFunction
import Definitions.Def_ForwardRM_Cutoffs_Cutoff

namespace ForwardRM.Cutoffs

/-- Equation (4.7) (Board–Skrzypacz, §4.2, p. 18): under weakly decreasing demand, the cutoff of
period `T − 1` solves `m(x^k_{T−1}) = δ E_T[max{m(x^k_{T−1}), m(v^k_T)}]`, where `v^k_T` is the
`k`-th highest value among the period-`T` entrants (if fewer than `k` buyers enter, the maximum is
`m(x^k_{T−1})`). -/
theorem cutoff_penultimate_equation (M : Model) (hD : M.DecreasingDemand) (hT : 2 ≤ M.T)
    (k : ℕ) (hk : 1 ≤ k) :
    M.m (M.cutoff (M.T - 1) k) =
      M.δ * M.expMaxWith M.T (M.m (M.cutoff (M.T - 1) k))
        (fun C => M.m ((sortDesc C).getD (k - 1) (M.cutoff (M.T - 1) k))) := by sorry

end ForwardRM.Cutoffs
