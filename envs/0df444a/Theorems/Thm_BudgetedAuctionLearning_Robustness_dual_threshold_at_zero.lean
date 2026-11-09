-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_dual_threshold_at_zero
-- name    : BudgetedAuctionLearning.Robustness.dual_threshold_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:01.77358+00:00
-- url     : https://prove2.me/theorems/bad00696-4a7c-492a-a9cf-7ff6ad03d78d
-- title:
--   Lemma 5.4 — value of the dual threshold at zero
-- statement:
--   For $\mu\ge0$ and $\rho_L>0$,
--
--   $$g^\star(0)=-\frac{E[v_O]-R^\star}{\rho_L}\le0.$$
--
--   When $E[v_L]>0$, this is a finite lower bound on $g^\star$ with Lemma 5.3. The generalized degenerate case $E[v_L]=0$ gives $-\infty$ on both sides.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - encoding: real-valued $f$, $R^\star$, $g^\star$ in the nondegenerate source setting → `EReal` values and division by the positive real $\rho_L$, with no `toReal` conversion in the equality; reason: the source instances have finite quantities; the generalization also permits $E[v_L]=0$, when (5) is empty and both sides of the equality are $-\infty$, rather than a default real zero
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.4, printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.4, printed p. 17 (PDF p. 18). -/
theorem dual_threshold_at_zero (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL μ : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) :
    dualThreshold fmt D ρL μ 0 =
        -(((meanOptimizerValue D : ℝ) : EReal) - lagrangianBenchmark fmt D ρL μ) / ((ρL : ℝ) : EReal) ∧
      dualThreshold fmt D ρL μ 0 ≤ 0 := by sorry

end BudgetedAuctionLearning.Robustness
