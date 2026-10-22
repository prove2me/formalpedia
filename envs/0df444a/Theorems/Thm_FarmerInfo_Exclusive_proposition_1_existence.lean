-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_1_existence
-- name    : FarmerInfo.Exclusive.proposition_1_existence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:04.768167+00:00
-- url     : https://prove2.me/theorems/a12499bc-209c-4fa5-9046-e819f474cbfb
-- title:
--   Proposition 1, p. 12 — the linear strategy profile is an equilibrium
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For every choice of informed farmers $I$, let $q_i(x_i,y)=A_0+A_1x_i+A_2y$ for $i\in I$ and $q_j(x_j)=B_0+B_1x_j$ for $j\notin I$, with the coefficients in equation (7). Then
--
--   $$\operatorname{BNE}(I,q).$$
--
--   This identifies an equilibrium for every information provision policy.
--
--   **Formalization Note** Equilibrium is tested against every measurable square-integrable strategy based on the farmer’s own observations, rather than only affine deviations.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 12, Proposition 1, equations (6)–(7)

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Proposition 1, p. 12: the displayed linear profile is an equilibrium. -/
theorem proposition_1_existence (M : Model) (hM : M.Standing) :
    ∀ I : Finset (Fin M.n), M.IsBNE I (M.linProfile I) := by sorry
end
end FarmerInfo.Exclusive
