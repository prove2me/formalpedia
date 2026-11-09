-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_pacing_budget_identity
-- name    : BudgetedAuctionLearning.Robustness.pacing_budget_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:29:20.446894+00:00
-- url     : https://prove2.me/theorems/4d4ea713-ffea-4999-9bc7-763d4d655952
-- title:
--   Lemma 3.1 — nonnegative pacing and exact payment identity
-- statement:
--   Let $\eta\in(0,1)$, $\rho_L>0$, $\lambda^{(1)}\ge0$, in either auction format, for arbitrary optimizer bids and learner values in $[0,1]$. Under the controller (3), every multiplier is nonnegative, and the learner's total payment through round $T$ is
--
--   $$\sum_{t=1}^Tp_L^{(t)}=\rho_LT+\frac{\lambda^{(1)}-\lambda^{(T+1)}}{\eta}.$$
--
--   If in addition $\lambda^{(1)}\le\rho_L$, the learner's cumulative payment after $T$ rounds is at most $\rho_LT$ for every $T$, so she never runs out of budget. This gives feasibility of the learner in the main theorem, without assuming it.
--
--   Differences from the source:
--   - generalization: with probability 1, for arbitrary optimizer behaviour → for every sequence of nonnegative bids and values in $[0,1]$; reason: the claim is pathwise; each realization of any optimizer strategy is such a sequence, so the probability-one claim follows
--   - encoding: 1-based rounds and $\lambda^{(T+1)}$ → 0-based rounds and `lam T`; reason: an index shift only
--   - reading: the learner never runs out of budget → cumulative payment at most $\rho_LT$ for every $T$; reason: this is what the source's proof establishes, $\lambda^{(T+1)}\ge\lambda^{(1)}$, and it implies the total budget bound at every horizon
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Lemma 3.1, printed p. 8 (PDF p. 9); proof printed p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_DualPotential
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Lemma 3.1, printed p. 8 (PDF p. 9). Pathwise, for arbitrary optimizer bids. The source index `T`
of `λ^(T+1)` is `lam T` here. -/
theorem pacing_budget_identity (fmt : AuctionFormat) (ρL η lam₁ : ℝ) (hρL : 0 < ρL) (hη₀ : 0 < η)
    (hη₁ : η < 1) (hlam₁ : 0 ≤ lam₁) (bO : ℕ → ℝ≥0) (vL : ℕ → I) :
    let lam := pacingController fmt ρL η lam₁ bO vL
    let pay : ℕ → ℝ := fun t => auctionPayL fmt (bO t) (lam t * (vL t : ℝ))
    (∀ t, 0 ≤ lam t) ∧
      (∀ T : ℕ, ∑ t ∈ Finset.range T, pay t = ρL * T + (lam₁ - lam T) / η) ∧
      (lam₁ ≤ ρL → ∀ T : ℕ, ∑ t ∈ Finset.range T, pay t ≤ ρL * T) := by sorry

end BudgetedAuctionLearning.Robustness
