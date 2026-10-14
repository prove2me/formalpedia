-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_s2_lt_s3
-- name    : EndogMerger.SymLoyal.s2_lt_s3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:52.580158+00:00
-- url     : https://prove2.me/theorems/a07e5961-214e-4c57-936b-2eb02c202371
-- title:
--   Proof of Proposition 2, PDF p. 47 — s₂ < s₃ for α < k < (1−2α)²/(2−5α)
-- statement:
--   Let $0<\alpha<1/3$ and $\alpha<k<(1-2\alpha)^2/(2-5\alpha)$. With $s_1=(1-3\alpha)(1-k/(1-2\alpha))$, $s_2=s_1(1-k/(\alpha+s_1))$ and $s_3=(1-3\alpha)(1-2k/(1-\alpha))$,
--   $$
--   s_2<s_3 .
--   $$
--
--   In the independent structure, $s_2$ switchers spill over to firm $A$; in the small merger, $s_3$ do. The inequality gives $L^{(0)}\le L^{(BC)}$ in Table A1's first row.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 2, PDF p. 47

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem s2_lt_s3 (α k : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < kCut α) :
    s2 α k < s3 α k := by sorry
end EndogMerger.SymLoyal
