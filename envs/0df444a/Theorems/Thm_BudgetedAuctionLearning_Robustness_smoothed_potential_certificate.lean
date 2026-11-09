-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_smoothed_potential_certificate
-- name    : BudgetedAuctionLearning.Robustness.smoothed_potential_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:15.345354+00:00
-- url     : https://prove2.me/theorems/0f6a9b7e-3e92-4ff4-8dd3-bab96d897746
-- title:
--   Lemma 5.8 — the smoothed potential meets the criterion of Lemma 5.1
-- statement:
--   Let $\mu\ge0$, $\rho_L>0$, $\eta\in(0,1)$, $\sigma>0$, $E[v_L]>0$, and suppose $g^\star(\bar\lambda)=0$ for some $\bar\lambda\ge\rho_L$. Then $G_\sigma$ of Eq. (18) satisfies both conditions of Lemma 5.1 with
--
--   $$A=R^\star+\mu\sigma-\eta\,\frac{\rho_L^2+\big(\frac{\bar\lambda-\eta\rho_L}{1-\eta}\big)^2}{\sigma}\,g^\star(0).$$
--
--   That is, $G_\sigma\ge0$ on $[0,\infty)$ and inequality (11) holds at this $A$. Together with Lemma 5.1 this gives the Lagrangian bound behind the main theorem.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge 0$, with $R^\star=R^\star(\mu)$; reason: the source's proof uses only that $R^\star$ is the supremum (5) at the given $\mu$, never its optimality; taking the Lemma 3.3 multiplier gives the source's statement
--   - reading: no separate hypothesis on $E[v_L]$ in the statement; $\mu$ comes from Lemma 3.3, which assumes positive expected values → hypothesis $0<E[v_L]$; reason: §5 works with the Lemma 3.3 multiplier and so inherits this; if $E[v_L]=0$ then (5) is infeasible, $R^\star=-\infty$ and $g^\star\equiv-\infty$, so the statement has no meaning. $E[v_O]>0$ is not needed and is not assumed
--   - encoding: real-valued $f$, $R^\star$, $g^\star$ → `EReal` suprema; exact `toReal` conversions of $R^\star$, $g^\star$ and $P_L$; reason: positive learner expectation makes these quantities finite, while unbounded first-price payments remain extended; the real constant A therefore uses the exact value of $R^\star$
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: "satisfies Lemma 5.1" → `PotentialCriterion`, which also records measurability of $G_\sigma$ on $[0,\infty)$; reason: measurability is the convention making (11) well defined, and $G_\sigma$ is continuous on $[0,\infty)$ under these hypotheses
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
--   - encoding: the tail integral defining $G_\sigma$ in (18) → a real Bochner tail integral of the interval average of `toReal` of $g^\star$; reason: positive learner expectation makes the monotone threshold finite on compact intervals; the zero-threshold hypothesis makes the average vanish beyond $\bar\lambda$, so the tail is integrable and neither integral uses a nonintegrability default
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.8, printed p. 19 (PDF p. 20); proof printed p. 20 (PDF p. 21)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.8, printed p. 19 (PDF p. 20): `G_σ` meets the criterion of Lemma 5.1 with the exact `A`. -/
theorem smoothed_potential_certificate (fmt : AuctionFormat) (D : Measure ValuePair)
    [IsProbabilityMeasure D] (ρL η μ sig lamBar : ℝ) (hρL : 0 < ρL) (hη₀ : 0 < η) (hη₁ : η < 1)
    (hμ : 0 ≤ μ) (hsig : 0 < sig) (hEL : 0 < meanLearnerValue D) (hlamBar : ρL ≤ lamBar)
    (hzero : dualThreshold fmt D ρL μ lamBar = 0) :
    PotentialCriterion fmt D ρL η μ (smoothedPotential fmt D ρL μ sig)
      ((lagrangianBenchmark fmt D ρL μ).toReal + μ * sig -
        η * ((ρL ^ 2 + ((lamBar - η * ρL) / (1 - η)) ^ 2) / sig) *
          (dualThreshold fmt D ρL μ 0).toReal) := by sorry

end BudgetedAuctionLearning.Robustness
