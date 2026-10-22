-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_2_one_gt_two
-- name    : FarmerInfo.Exclusive.proposition_2_one_gt_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:59.10198+00:00
-- url     : https://prove2.me/theorems/f6533319-80e1-42cb-b049-207929ccd591
-- title:
--   Proof of Proposition 2, p. 36 — one informed farmer beats two
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   The closed-form farmer welfare with one public-signal recipient is strictly greater than with two:
--
--   $$W(1,\beta;\gamma)>W(2,\beta;\gamma).$$
--
--   Together with the decline beyond two, this leaves zero and one informed farmer as the planner’s candidates.
--
--   **Formalization Note** The paper’s displayed expression for the difference omits its positive denominator. The Lean statement preserves the source’s sign claim under $n\geq4$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 36, Appendix A, Proof of Proposition 2, welfare difference W(1) − W(2)

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Appendix A, p. 36: one informed farmer beats two. -/
theorem proposition_2_one_gt_two (M : Model) (hM : M.Standing) :
    M.W 2 < M.W 1 := by sorry
end
end FarmerInfo.Exclusive
