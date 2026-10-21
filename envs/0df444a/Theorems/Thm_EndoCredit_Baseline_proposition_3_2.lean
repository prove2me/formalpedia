-- Prove2me | Theorems.Thm_EndoCredit_Baseline_proposition_3_2
-- name    : EndoCredit.Baseline.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:41.865987+00:00
-- url     : https://prove2.me/theorems/7809518c-d3e3-4396-9043-d2bb7f023398
-- title:
--   Proposition 3.2, p. 11 — optimal wealth obeys the endogenous credit limit
-- statement:
--   In the baseline limited-commitment household problem, let initial income be $\bar I>0$ and initial wealth be $x$. If $x\ge-m^*\bar I$, the initial multiplier equation has a unique admissible solution $y_0^*$. Its shadow-price consumption process is feasible and maximizes expected utility among all feasible plans. The conditional present value $X_t^*$ of that plan's future net consumption has the closed form
--
--   $$X_t^*=\frac{I_t}{K}\left(\frac{y_t^*}{1+D_t^*}\right)^{-1/\gamma}-\frac{I_t}{r_I}+\frac{\delta^{1-\gamma}\alpha_+Q^{\gamma\alpha_+}}{\hat\beta(\alpha_+-1)(1-\gamma+\gamma\alpha_+)}\left(\frac{y_t^*}{1+D_t^*}\right)^{\alpha_+-1}I_t\ge-m^*I_t,$$
--
--   for every $t\ge0$, almost surely. If $x<-m^*\bar I$, no consumption plan satisfies both the static budget and all participation constraints, so immediate default is the household's option. The result identifies $m^*I_t$ as the endogenous credit limit.
--
--   **Formalization Note** The problem is the static martingale form used by §3 because Problem 2.2's default time is undefined. $H_t$ and $I_t$ are the explicit GBM solutions; two independent Brownian coordinates generate the uncompleted natural filtration. The statement requires genuine integrability of each conditional present value. The standing conditions add $\hat\beta>0$ and a positive coefficient in the $\alpha_+$ quadratic; $y_0^*\le Q^{-\gamma}$ enforces $D_0^*=0$. Optimal wealth is defined by the conditional present value, independently of the displayed formula.
-- source:
--   Choi, Koo, Lim & Yoo, Endogenous Credit, Business Cycle, and Portfolio Selection, SSRN 2560607, https://ssrn.com/abstract=2560607 (version of October 25, 2023), p. 11, Proposition 3.2 and (3.10)

import Mathlib
import Definitions.Def_EndoCredit_Baseline_Candidate

open MeasureTheory
open scoped NNReal

namespace EndoCredit.Baseline

/-- Proposition 3.2 in the static martingale formulation of Problem 2.2. Financial
wealth is a conditional present value of the optimal plan, not the right side of (3.10). -/
theorem proposition_3_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : BrownianPath Ω) (hW : EthierKurtz.IsStandardBrownian P W)
    (p : Params) (hp : p.Standing) (x : ℝ) :
    (-(mStar p) * p.Ibar ≤ x →
      (∃! y0 : ℝ, y0 ∈ Set.Ioc 0 (ybar p) ∧ x / p.Ibar = phi p y0) ∧
      ∀ y0 ∈ Set.Ioc 0 (ybar p), x / p.Ibar = phi p y0 →
        cStar p W y0 ∈ Feasible p P W hW x ∧
        IsGreatest (J0 p P '' Feasible p P W hW x) (J0 p P (cStar p W y0)) ∧
        ∀ t : ℝ≥0,
          Integrable (pvNet p W (cStar p W y0) t) P ∧
          (P[pvNet p W (cStar p W y0) t | filtration P W hW t] =ᵐ[P]
            wealthCF p W y0 t) ∧
          (∀ᵐ ω ∂P, -(mStar p) * inc p W t ω ≤
            P[pvNet p W (cStar p W y0) t | filtration P W hW t] ω)) ∧
    (x < -(mStar p) * p.Ibar → Feasible p P W hW x = ∅) := by sorry

end EndoCredit.Baseline
