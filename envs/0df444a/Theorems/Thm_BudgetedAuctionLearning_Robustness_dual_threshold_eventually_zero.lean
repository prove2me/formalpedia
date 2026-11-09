-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_dual_threshold_eventually_zero
-- name    : BudgetedAuctionLearning.Robustness.dual_threshold_eventually_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:07.93398+00:00
-- url     : https://prove2.me/theorems/65bf0295-d920-42d5-aa06-1cdf0116d65b
-- title:
--   Lemma 5.5 — the dual threshold eventually vanishes
-- statement:
--   Let $\mu\ge0$, $\rho_L>0$ and $E[v_L]>0$. Suppose either that $P[0<v_L<v_O\varepsilon]=0$ for some $\varepsilon>0$, or that $R^\star>E[v_O\mathbf 1_{v_L=0}]$. Then there is a finite $\bar\lambda\ge0$ with $g^\star(\bar\lambda)=0$.
--
--   This makes the potential finite, and it is where the distributional assumption of the main theorem enters.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - encoding: real-valued $f$, $R^\star$, $g^\star$ → `EReal` suprema, with the strict second branch comparing $E[v_O\mathbf 1_{v_L=0}]$ to $R^\star$ in `EReal`; reason: under $E[v_L]>0$, $R^\star$ and $g^\star$ are finite; extended payment integrals still allow unbounded first-price bids, and no `toReal` conversion is used in this conclusion
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.5, printed p. 17 (PDF p. 18); proof printed pp. 17–18 (PDF pp. 18–19)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.5, printed p. 17 (PDF p. 18). -/
theorem dual_threshold_eventually_zero (fmt : AuctionFormat) (D : Measure ValuePair)
    [IsProbabilityMeasure D] (ρL μ : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) (hEL : 0 < meanLearnerValue D)
    (hcase : (∃ ε : ℝ, 0 < ε ∧ ValueGap D ε) ∨
      ((zeroLearnerValueMass D : ℝ) : EReal) < lagrangianBenchmark fmt D ρL μ) :
    ∃ lamBar : ℝ, 0 ≤ lamBar ∧ dualThreshold fmt D ρL μ lamBar = 0 := by sorry

end BudgetedAuctionLearning.Robustness
