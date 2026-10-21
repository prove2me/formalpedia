-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_1_Q_lt_one
-- name    : EndoCredit.Baseline.proposition_3_1_Q_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:53.455278+00:00
-- url     : https://prove2.me/theorems/c5fe424d-f5ba-4651-8d4d-2a81f2a18eb6
-- title:
--   Proposition 3.1, p. 10 — Q < 1 clause
-- statement:
--   For the parameter range $0<\delta\le\bar\delta$, define $Q$ as in Proposition 3.1. Then $Q$ is positive and strictly less than one:
--
--   $$0<Q=\delta\left(\frac{K\alpha_+\gamma}{(1-\gamma+\gamma\alpha_+)\hat\beta}\right)^{1/(1-\gamma)}<1.$$
--
--   This is the scale of the consumption-to-income floor when the participation constraint binds.
--
--   **Formalization Note** Positivity is stated explicitly. The standing conditions include the two nondegeneracy conditions needed for the real powers and quadratic root.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 10, Proposition 3.1, Q < 1 clause

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- The `Q < 1` clause of Proposition 3.1, with positivity made explicit. -/
theorem proposition_3_1_Q_lt_one (p : Params) (hp : p.Standing) :
    0 < Q p ∧ Q p < 1 := by sorry

end EndoCredit.Baseline
