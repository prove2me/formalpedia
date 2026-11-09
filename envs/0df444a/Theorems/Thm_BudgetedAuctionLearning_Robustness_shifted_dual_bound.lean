-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_shifted_dual_bound
-- name    : BudgetedAuctionLearning.Robustness.shifted_dual_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:47.771087+00:00
-- url     : https://prove2.me/theorems/2ae1e0db-f4f2-4b0b-90b0-fe9f37609c71
-- title:
--   Lemma 5.6 — dual bound at a shifted threshold
-- statement:
--   Let $\mu\ge0$, $\rho_L>0$, $E[v_L]>0$, and fix a signed perturbation $\varepsilon$ with $\lambda\ge0$ and $\lambda+\varepsilon\ge0$. Then
--
--   $$f\big(\lambda,g^\star(\lambda+\varepsilon)\big)\le R^\star+\mu\varepsilon^+-g^\star(0)\varepsilon^-,$$
--
--   where $\varepsilon^+=\max\{\varepsilon,0\}$ and $\varepsilon^-=\max\{-\varepsilon,0\}$. Using a slightly wrong multiplier therefore costs only a linear error in $f$.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - reading: no separate hypothesis on $E[v_L]$ in the statement; $\mu$ comes from Lemma 3.3, which assumes positive expected values → hypothesis $0<E[v_L]$; reason: §5 works with the Lemma 3.3 multiplier and so inherits this; if $E[v_L]=0$ then (5) is infeasible, $R^\star=-\infty$ and $g^\star\equiv-\infty$, so the statement has no meaning. $E[v_O]>0$ is not needed and is not assumed
--   - encoding: real-valued $f$, $R^\star$, $g^\star$ → `EReal` values; `toReal` applied only to $g^\star$ and $P_L$, which are finite here; reason: first-price payments can be $+\infty$; the extended values make that case and the empty cases explicit instead of defaulting to $0$
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.6, printed p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.6, printed p. 18 (PDF p. 19). `E[v_L] > 0` makes `g★` finite, as the source's use of the
Lemma 3.3 multiplier presupposes. -/
theorem shifted_dual_bound (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL μ : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) (hEL : 0 < meanLearnerValue D) (lam ε : ℝ) (hlam : 0 ≤ lam)
    (hlamε : 0 ≤ lam + ε) :
    dualFunction fmt D ρL μ lam (dualThreshold fmt D ρL μ (lam + ε)).toReal ≤
      lagrangianBenchmark fmt D ρL μ +
        ((μ * max ε 0 - (dualThreshold fmt D ρL μ 0).toReal * max (-ε) 0 : ℝ) : EReal) := by sorry

end BudgetedAuctionLearning.Robustness
