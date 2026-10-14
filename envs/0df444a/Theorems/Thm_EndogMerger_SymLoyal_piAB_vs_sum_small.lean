-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_piAB_vs_sum_small
-- name    : EndogMerger.SymLoyal.piAB_vs_sum_small
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:58.288037+00:00
-- url     : https://prove2.me/theorems/641b3f57-8a8f-40f4-b551-306efaa31ccf
-- title:
--   Proof of Proposition 3, PDF p. 49 — Π^(AB) vs Π^(BC)_A+Π^(BC)_B: threshold k* below (1−α)/2, iff k < (1−2α)²/(1−α) above
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$, $r>0$ and $k^*=\alpha(1-2\alpha)/(1-3\alpha)$. With the Table A1 profits:
--
--   1. if $k<(1-\alpha)/2$: $k>k^*$ implies $\Pi^{(AB)}>\Pi^{(BC)}_A+\Pi^{(BC)}_B$, and $k<k^*$ implies $\Pi^{(AB)}<\Pi^{(BC)}_A+\Pi^{(BC)}_B$;
--   2. if $(1-\alpha)/2<k$:
--   $$
--   \Pi^{(AB)}>\Pi^{(BC)}_A+\Pi^{(BC)}_B\iff k<\frac{(1-2\alpha)^2}{1-\alpha}.
--   $$
--
--   This decides the first disjunct of (1b) and condition (2b), the comparison of the mixed and small mergers from the point of view of firms $A$ and $B$.
--
--   **Formalization Note** The point $k=(1-\alpha)/2$ is excluded, as on the page.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF pp. 48–49

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem piAB_vs_sum_small (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (k < (1 - α) / 2 →
      (kStar α < k → piBCA α k r + piBCB α k r < piAB α k r) ∧
      (k < kStar α → piAB α k r < piBCA α k r + piBCB α k r)) ∧
    ((1 - α) / 2 < k →
      (piBCA α k r + piBCB α k r < piAB α k r ↔ k < (1 - 2 * α) ^ 2 / (1 - α))) := by sorry
end EndogMerger.SymLoyal
