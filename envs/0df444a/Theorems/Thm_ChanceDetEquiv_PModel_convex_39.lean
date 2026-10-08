-- Prove2me | Theorems.Thm_ChanceDetEquiv_PModel_convex_39
-- name    : ChanceDetEquiv.PModel.convex_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:18.336634+00:00
-- url     : https://prove2.me/theorems/a073455e-86e1-4e16-b927-7e6b12f644c4
-- title:
--   Eq. (39) — the transformed P-model feasible set is convex
-- statement:
--   For positive row and decision dimensions, P-model data and integrable moments, let $F_{39}$ contain all $(\bar D,\bar v,\bar v_0,\bar w_0,t)$ satisfying every constraint of program (39), including $\bar w_0=1$, $t\ge0$, and all $\bar v_i\ge0$. Then
--   $$
--   F_{39}\text{ is a convex subset of the product space of its decision variables.}
--   $$
--   The claim includes points with $t=0$, which are needed when comparing suprema of the two programs.
--
--   **Formalization Note** The fourth constraint uses $\bar v_i^2\ge K_i^2(\bar\sigma_i^2-\bar\mu_i^2)$ with $\bar\sigma_i^2$ the raw second moment in (39b), not the centered variance. The paper's $K_i=\Phi^{-1}(\alpha_i)$ has $\alpha_i\in(1/2,1)$, and the row residuals have Gaussian laws.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), pp. 32–33, Eqs. (39)–(39b) and paragraph after (39b); https://doi.org/10.1287/opre.11.1.18

import Definitions.Def_ChanceDetEquiv_PModel_Model

namespace ChanceDetEquiv.PModel

open MeasureTheory

/-- The feasible set of the transformed P-model program (39), including t = 0, is convex. -/
theorem convex_39 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d) :
    Convex ℝ (feasible39 d) := by sorry

end ChanceDetEquiv.PModel
