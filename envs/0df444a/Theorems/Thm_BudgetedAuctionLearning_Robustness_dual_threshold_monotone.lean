-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_dual_threshold_monotone
-- name    : BudgetedAuctionLearning.Robustness.dual_threshold_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:33.530889+00:00
-- url     : https://prove2.me/theorems/7b3d5629-8156-4601-b5fe-914700c609ff
-- title:
--   Lemma 5.3 — monotonicity of the dual threshold
-- statement:
--   For $\mu\ge0$ and $\rho_L>0$, the threshold $g^\star$ of Eq. (14) is weakly increasing on $[0,\infty)$:
--
--   $$0\le\lambda_1\le\lambda_2\implies g^\star(\lambda_1)\le g^\star(\lambda_2).$$
--
--   When $E[v_L]>0$, Lemma 5.4 gives a finite lower bound, and monotonicity gives integrability on compact intervals. In the generalized case $E[v_L]=0$, the threshold is identically $-\infty$.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - encoding: $g^\star$ with value $-\infty$ on an empty set → `EReal`-valued `dualThreshold`, with `MonotoneOn` on $[0,\infty)$; reason: this is the source's own convention; the physical domain is $\lambda\ge0$
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.3, printed p. 15 (PDF p. 16); proof printed pp. 15–17 (PDF pp. 16–18)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.3, printed p. 15 (PDF p. 16). -/
theorem dual_threshold_monotone (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL μ : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) :
    MonotoneOn (dualThreshold fmt D ρL μ) (Set.Ici 0) := by sorry

end BudgetedAuctionLearning.Robustness
