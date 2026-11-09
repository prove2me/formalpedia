-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_dual_separate_convexity
-- name    : BudgetedAuctionLearning.Robustness.dual_separate_convexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:32.132951+00:00
-- url     : https://prove2.me/theorems/b1286a01-1013-43f6-bfa0-1c9b64918537
-- title:
--   Claim 5.2 — separate convexity of the dual function
-- statement:
--   For $\mu\ge0$ the dual function $f(\lambda,g)$ is convex in $\lambda\ge0$ for each fixed real $g$, and convex in real $g$ for each fixed $\lambda\ge0$: for $t\in[0,1]$,
--
--   $$f(t\lambda_1+(1-t)\lambda_2,g)\le tf(\lambda_1,g)+(1-t)f(\lambda_2,g),\quad f(\lambda,tg_1+(1-t)g_2)\le tf(\lambda,g_1)+(1-t)f(\lambda,g_2).$$
--
--   Convexity in $g$ makes the set defining $g^\star$ an interval and is used for the smoothed threshold.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge0$, without positive-expectation assumptions; reason: on the physical domain, the supremum of the affine Lagrangian expressions gives both Jensen inequalities for every nonnegative multiplier, independently of R^\star or multiplier optimality; the source's multiplier and value law are included
--   - reading: $f:\mathbb R^2\to\mathbb R$ → the physical domain $\lambda\ge0$, $g$ real; reason: for $\lambda<0$ the penalty is a reward, the first-price supremum is $+\infty$ and real $f$ is undefined; the source uses only $\lambda\ge0$
--   - reading: "(but not necessarily jointly convex)" → not stated; reason: it is a remark that joint convexity is not claimed, not a property asserted of every instance
--   - encoding: convexity of a real function → explicit Jensen inequalities in `EReal`; reason: `ConvexOn` does not apply to `EReal`; $f$ is finite, so these are the usual inequalities
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Claim 5.2, printed p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Claim 5.2, printed p. 15 (PDF p. 16): `f` is convex in `λ ≥ 0` for fixed `g` and convex in real `g`
for fixed `λ ≥ 0`. Stated as extended-real Jensen inequalities. -/
theorem dual_separate_convexity (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL μ : ℝ) (hρL : 0 < ρL) (hμ : 0 ≤ μ) :
    (∀ g lam₁ lam₂ t : ℝ, 0 ≤ lam₁ → 0 ≤ lam₂ → 0 ≤ t → t ≤ 1 →
      dualFunction fmt D ρL μ (t * lam₁ + (1 - t) * lam₂) g ≤
        (t : EReal) * dualFunction fmt D ρL μ lam₁ g +
          ((1 - t : ℝ) : EReal) * dualFunction fmt D ρL μ lam₂ g) ∧
    (∀ lam g₁ g₂ t : ℝ, 0 ≤ lam → 0 ≤ t → t ≤ 1 →
      dualFunction fmt D ρL μ lam (t * g₁ + (1 - t) * g₂) ≤
        (t : EReal) * dualFunction fmt D ρL μ lam g₁ +
          ((1 - t : ℝ) : EReal) * dualFunction fmt D ρL μ lam g₂) := by sorry

end BudgetedAuctionLearning.Robustness
