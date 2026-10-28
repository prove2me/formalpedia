-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_2_mstar_nonneg
-- name    : EndoCredit.Baseline.proposition_3_2_mstar_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:48.046815+00:00
-- url     : https://prove2.me/theorems/f86ecba9-e599-42c7-82ce-4799fde21a9a
-- title:
--   Proposition 3.2, p. 11 — nonnegative credit-limit coefficient
-- statement:
--   The coefficient $m^*$ multiplying income in the endogenous borrowing limit is nonnegative and smaller than the coefficient of the natural borrowing limit:
--
--   $$0\le m^*=\frac1{r_I}-\frac{1-\gamma+\alpha_+\gamma}{\gamma K(\alpha_+-1)}Q<\frac1{r_I}.$$
--
--   Thus participation constraints permit no more debt against income than the natural present-value bound.
--
--   **Formalization Note** The strict upper bound is the paper's comparison with the natural limit in (2.4) and the abstract; the proposition itself prints only $m^*\ge0$.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 11, Proposition 3.2, m* ≥ 0 clause; p. 6, (2.4)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- The nonnegative credit limit in Proposition 3.2, below the natural limit. -/
theorem proposition_3_2_mstar_nonneg (p : Params) (hp : p.Standing) :
    0 ≤ mStar p ∧ mStar p < 1 / rI p := by sorry

end EndoCredit.Baseline
