-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_3_lambda_star
-- name    : EndoCredit.Baseline.proposition_3_3_lambda_star
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:51.432156+00:00
-- url     : https://prove2.me/theorems/ed73e9bb-4b7b-4ff7-9fa9-61c81d1ac057
-- title:
--   Proposition 3.3, p. 11 — admissible branch of the initial multiplier equation
-- statement:
--   Given initial wealth $x$ and initial income $\bar I>0$, write $y_0^*=\lambda^*\bar I^\gamma$. The initial-multiplier equation of Proposition 3.3 is $x/\bar I=\phi(y_0^*)$. It has exactly one solution in the branch required by $D_0^*=0$ when $x\ge-m^*\bar I$, and none there below the credit limit:
--
--   $$x\ge-m^*\bar I\ \Longrightarrow\ \exists!\,y_0^*\in(0,Q^{-\gamma}]\text{ with }\frac{x}{\bar I}=\phi(y_0^*).$$
--
--   This selects the multiplier used to define the optimal candidate process.
--
--   **Formalization Note** The printed equation alone can have another root above $Q^{-\gamma}$. The branch restriction makes explicit the paper's requirement $D_0^*=0$, and the negative case records nonexistence on that branch.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 11, Proposition 3.3, λ* equation; p. 8, D₀ = 0

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Model

namespace EndoCredit.Baseline

/-- The financially admissible branch of the initial multiplier equation in Proposition 3.3. -/
theorem proposition_3_3_lambda_star (p : Params) (hp : p.Standing) (x : ℝ) :
    (-(mStar p) * p.Ibar ≤ x →
      ∃! y0 : ℝ, y0 ∈ Set.Ioc 0 (ybar p) ∧ x / p.Ibar = phi p y0) ∧
    (x < -(mStar p) * p.Ibar →
      ¬∃ y0 : ℝ, y0 ∈ Set.Ioc 0 (ybar p) ∧ x / p.Ibar = phi p y0) := by sorry

end EndoCredit.Baseline
