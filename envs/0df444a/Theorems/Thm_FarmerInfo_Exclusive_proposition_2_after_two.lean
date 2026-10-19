-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_2_after_two
-- name    : FarmerInfo.Exclusive.proposition_2_after_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:50.749063+00:00
-- url     : https://prove2.me/theorems/cc088c32-d03c-4cba-be2c-25f60c277360
-- title:
--   Proof of Proposition 2, p. 36 — welfare decreases from two informed farmers onward
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For the real extension $W(t)$ of the closed-form total profit, the derivative numerator at two informed farmers is negative, and $W$ is strictly decreasing over the feasible policy range $[2,n]$:
--
--   $$\Omega_n(2)<0,\qquad 2\leq t_1<t_2\leq n\Longrightarrow W(t_2)<W(t_1).$$
--
--   This eliminates every policy with more than two informed farmers from the planner’s optimum.
--
--   **Formalization Note** The page needs $n\geq3$ for the displayed sign; the base model assumes $n\geq4$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 36, Appendix A, Proof of Proposition 2, display for Ω_n(2, β; γ)

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Appendix A, p. 36: welfare falls strictly from two through the policy limit. -/
theorem proposition_2_after_two (M : Model) (hM : M.Standing) :
    M.Omega_n 2 < 0 ∧
      StrictAntiOn M.W (Set.Icc (2 : ℝ) (M.n : ℝ)) := by sorry
end
end FarmerInfo.Exclusive
