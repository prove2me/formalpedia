-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_2_one_minus_zero
-- name    : FarmerInfo.Exclusive.proposition_2_one_minus_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:06.112362+00:00
-- url     : https://prove2.me/theorems/50058f6f-6f3d-4e6a-baf3-de7ea92e3b53
-- title:
--   Proof of Proposition 2, p. 36 — welfare difference between one recipient and none
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   The exact difference between one public-signal recipient and none is
--
--   $$W(1,\beta;\gamma)-W(0,\beta;\gamma)=\frac{\beta V(n,\beta;\gamma)}{b(2\alpha+\gamma+n\gamma)^2[4\alpha^2+(1+n)\gamma(\beta+\gamma)+2\alpha(2\beta+(2+n)\gamma)]^2}.$$
--
--   The denominator is positive in the base model, so the sign of this difference is the sign of $V$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 36, Appendix A, Proof of Proposition 2, final displayed welfare difference

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Appendix A, p. 36: the exact welfare difference between one and none. -/
theorem proposition_2_one_minus_zero (M : Model) (hM : M.Standing) :
    M.W 1 - M.W 0 =
      M.β * M.V /
        (M.b * (2 * M.α + M.γ + (M.n : ℝ) * M.γ) ^ 2 *
          (4 * M.α ^ 2 + (1 + (M.n : ℝ)) * M.γ * (M.β + M.γ) +
            2 * M.α * (2 * M.β + (2 + (M.n : ℝ)) * M.γ)) ^ 2) := by sorry
end
end FarmerInfo.Exclusive
