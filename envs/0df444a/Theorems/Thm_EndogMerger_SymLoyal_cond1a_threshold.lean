-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_cond1a_threshold
-- name    : EndogMerger.SymLoyal.cond1a_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:00.151677+00:00
-- url     : https://prove2.me/theorems/c8a7d5d3-5448-4236-9235-3861e78ca1cb
-- title:
--   Proof of Proposition 3, PDF p. 48 — Π^(AB) < Π^(0)_A + Π^(0)_B for k < α(1−2α)/(1−3α), reversed for k > α(1−2α)/(1−3α)
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$, $r>0$, and $k^*=\alpha(1-2\alpha)/(1-3\alpha)$. With the Table A1 profits,
--
--   1. if $k<k^*$, then $\Pi^{(AB)}<\Pi^{(0)}_A+\Pi^{(0)}_B$;
--   2. if $k>k^*$, then
--   $$
--   \Pi^{(AB)}>\Pi^{(0)}_A+\Pi^{(0)}_B .
--   $$
--
--   So condition (1a), the profitability of the mixed merger for firms $A$ and $B$, holds exactly when $k>k^*$ in the limited-capacity range.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 48

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem cond1a_threshold (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (k < kStar α → piAB α k r < piIndepA α k r + piIndepB α k r) ∧
    (kStar α < k → piIndepA α k r + piIndepB α k r < piAB α k r) := by sorry
end EndogMerger.SymLoyal
