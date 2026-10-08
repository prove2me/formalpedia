-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_midpoint_G_bound
-- name    : ChoicePAC.MidPoint.midpoint_G_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:46.815576+00:00
-- url     : https://prove2.me/theorems/541bf469-ee65-40cc-ac01-3e6b9bbdf117
-- title:
--   App. C.6, p. 344 — $G(k,t) \le 4(1-t)$ for mid-point re-solving (before the last re-solve)
-- statement:
--   Consider the mid-point schedule of the $k$-th system, $t_l = 1 - 2^{-l}$, $l = 1,\dots,M^k$, with $M^k$ the smallest integer such that $2^{-M^k} \le 1/k$. For every $k \ge 1$ and every $t$ with $0 \le t < t_{M^k}$,
--   $$G(k,t) \le 4(1-t).$$
--
--   This estimate is what turns the general bound (8) into the constant bound of Theorem 5.2.
--
--   **Formalization Note** The page asserts the bound "for all $t \in [0,1]$". That is false on $[t_{M^k}, 1)$: for $k = 2$, $M = 1$, $t_1 = 1/2$ and $t = 0.99$, $G = 0.49 + 0.5\cdot(0.01)^2/(0.5)^2 = 0.4902 > 0.04 = 4(1-t)$. The display's own range $1 - 2^{-(i-1)} \le t < 1 - 2^{-i}$ uses $t_i = 1 - 2^{-i}$, valid only for $i \le M^k$, so the corrected statement covers $t < t_{M^k}$. For $k = 1$ there is no re-solve ($M = 0$) and the range is empty.
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, App. C.6, p. 344, first display

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_GF

namespace ChoicePAC.MidPoint
theorem midpoint_G_bound (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t < (midpointSchedule k).time (midpointSchedule k).M) :
    (midpointSchedule k).G t ≤ 4 * (1 - t) := by sorry
end ChoicePAC.MidPoint
