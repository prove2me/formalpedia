-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_sigma_step
-- name    : EndogMerger.SymLoyal.sigma_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:56.200294+00:00
-- url     : https://prove2.me/theorems/4335dbf4-8fa5-477e-81e0-ae6b013ee5b4
-- title:
--   Proof of Proposition 3, PDF p. 48 — r(2α+s₁) > r(1−2α+k)(α+s₂)/(1−2α) for α < k < (1−2α)²/(2−5α)
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<(1-2\alpha)^2/(2-5\alpha)$ and $r>0$. Then
--   $$
--   r(2\alpha+s_1)\ >\ \frac{r(1-2\alpha+k)(\alpha+s_2)}{1-2\alpha}.
--   $$
--
--   The right side is the first branch of $\Pi^{(0)}_A+\Pi^{(0)}_B=(1-2\alpha+k)L^{(0)}$ in Table A1's first row and the left side is the first branch of $\Pi^{(AB)}$, so the sign of $\Pi^{(AB)}-(\Pi^{(0)}_A+\Pi^{(0)}_B)$ reduces to a comparison of $r(2\alpha+s_1)$ with $r\alpha(1-2\alpha+k)/k$.
--
--   **Formalization Note** The paper's displayed identity for the difference omits a factor $r$ on its right side; the inequality stated here is unaffected.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 48

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem sigma_step (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < kCut α) (hr : 0 < r) :
    r * (1 - 2 * α + k) * (α + s2 α k) / (1 - 2 * α) < r * (2 * α + s1 α k) := by sorry
end EndogMerger.SymLoyal
