-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_bellman_potential_bound
-- name    : BudgetedAuctionLearning.Robustness.bellman_potential_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:28.254925+00:00
-- url     : https://prove2.me/theorems/7a159072-765f-47cb-9fae-19a6b4d9167b
-- title:
--   Lemma 5.1 — potential upper bound on the Bellman value
-- statement:
--   Let $\mu\ge0$, $\rho_L>0$, $\eta\in(0,1)$. Let $G$ be a nonnegative potential on $[0,\infty)$ and let $A$ be a real number such that, for all $\lambda\ge0$,
--
--   $$A\ge\sup_{\hat v_O}\Big(U_O(\hat v_O)-\mu\lambda P_O(\hat v_O)+\frac1\eta E\big[G\big(\lambda+\eta(\rho_L-\lambda P_L(\hat v_O,v_L,v_O))\big)-G(\lambda)\big]\Big).\tag{11}$$
--
--   Then for every integer $\tau\ge0$ and $\lambda\ge0$,
--
--   $$R_\tau(\lambda)\le A\tau+\frac1\eta G(\lambda).\tag{10}$$
--
--   This separates the horizon from the multiplier, which is the form the main theorem's proof instantiates.
--
--   Differences from the source:
--   - generalization: $\mu$ is the optimal multiplier of Lemma 3.3 (which assumes $E[v_L],E[v_O]>0$) → every $\mu\ge0$, without positive-expectation assumptions; reason: the induction on the actual Bellman recursion uses only nonnegativity of the potential and the one-step criterion, and does not involve R^\star, optimality of the multiplier, or positive expected values; the source's multiplier and value law are included
--   - encoding: $G$ with expectations understood to be well defined → `PotentialCriterion`, with $G$ measurable on $[0,\infty)$ and $E[G(\cdot)]$ an `ℝ≥0∞` integral; reason: measurability is the implicit convention behind the expectation in (11); an infinite expectation violates (11) unless the penalty term is already $-\infty$
--   - encoding: fake-value maps in $\mathbb R_{\ge0}^{[0,1]}$ → measurable maps `FakeValue`; reason: the source's expectations need measurability; this is its standing convention
--   - encoding: $R_\tau$ with a real expectation → `EReal` Bellman recursion integrating `toENNReal`; reason: $R_\tau\in[0,\tau]$ on $\lambda\ge0$, so the conversion is exact, and $R_\tau$ is Borel
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 5.1, printed pp. 13–14 (PDF pp. 14–15)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 5.1, printed pp. 13–14 (PDF pp. 14–15). -/
theorem bellman_potential_bound (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL η μ : ℝ) (hρL : 0 < ρL) (hη₀ : 0 < η) (hη₁ : η < 1) (hμ : 0 ≤ μ) (G : ℝ → ℝ) (A : ℝ)
    (hG : PotentialCriterion fmt D ρL η μ G A) (τ : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    bellmanValue fmt D ρL η μ τ lam ≤ ((A * τ + (1 / η) * G lam : ℝ) : EReal) := by sorry

end BudgetedAuctionLearning.Robustness
