-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_bse_strong_duality
-- name    : BudgetedAuctionLearning.Robustness.bse_strong_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:00.96884+00:00
-- url     : https://prove2.me/theorems/96ad4073-aa2d-4f38-920f-754df266a373
-- title:
--   Lemma 3.3 — strong duality for the budgeted Stackelberg program
-- statement:
--   Let $\rho_L,\rho_O>0$ and suppose both players have positive expected values, $E[v_L]>0$ and $E[v_O]>0$. Then there is a finite $\mu\ge0$ with
--
--   $$\mathrm{OPT}=R^\star(\mu)+\mu\rho_O,$$
--
--   where $R^\star(\mu)$ is the supremum of Optimization Program (5), and this $\mu$ minimizes $\mu'\mapsto R^\star(\mu')+\mu'\rho_O$ over $\mu'\ge0$ (footnote 4). This replaces the budgeted value by a Lagrangian reward in the rest of the analysis.
--
--   Differences from the source:
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
--   - encoding: real-valued programs (4), (5) → `EReal` suprema with `ℝ≥0∞` payments and $0\cdot\infty=0$; reason: first-price payments can be $+\infty$; this keeps every source instance and leaves no default value
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 3.3 and footnote 4, printed p. 9 (PDF p. 10); proof printed pp. 27–28 (PDF pp. 28–29)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 3.3, printed p. 9 (PDF p. 10), with footnote 4. -/
theorem bse_strong_duality (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL ρO : ℝ) (hρL : 0 < ρL) (hρO : 0 < ρO) (hEL : 0 < meanLearnerValue D)
    (hEO : 0 < meanOptimizerValue D) :
    ∃ μ : ℝ, 0 ≤ μ ∧
      bseValue fmt D ρL ρO = lagrangianBenchmark fmt D ρL μ + ((μ * ρO : ℝ) : EReal) ∧
      ∀ μ' : ℝ, 0 ≤ μ' →
        lagrangianBenchmark fmt D ρL μ + ((μ * ρO : ℝ) : EReal) ≤
          lagrangianBenchmark fmt D ρL μ' + ((μ' * ρO : ℝ) : EReal) := by sorry

end BudgetedAuctionLearning.Robustness
