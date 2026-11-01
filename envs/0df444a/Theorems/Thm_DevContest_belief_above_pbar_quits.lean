-- Prove2me | Theorems.Thm_DevContest_belief_above_pbar_quits
-- name    : DevContest.belief_above_pbar_quits
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:54:51.595756+00:00
-- url     : https://prove2.me/theorems/1f28d3c9-4742-4d64-875a-9574f080ff60
-- title:
--   Proof of Theorem 2, p.ec19 — no belief above $\bar p$ supports effort
-- statement:
--   Let $\lambda,c>0$ and $2c/\lambda<\bar R<3c/\lambda$. For every $p\in(\bar p,1]$ and every measurable first-stage effort $y$ of the rival with values in $[0,1]$,
--   $$
--   V_{1,p}=pV_{1,1}+(1-p)V_{1,0}\le p\,\tfrac12\Bigl(\bar R-\frac c\lambda\Bigr)+(1-p)\Bigl(\bar R-\frac c\lambda\Bigr)<\frac c\lambda .
--   $$
--   Consequently an agent with no success whose continuation payoff has this form at every date optimally quits: in the problem (EC.39) zero effort has value $0$, and every effort path has a nonpositive value.
--
--   So the constraint $p\le\bar p$ cannot be relaxed by any first-stage effort of the rival.
--
--   Differences from the source:
--   - generalization: in the case $\bar R>7c/(3\lambda)$ → for all $\bar R\in(2c/\lambda,3c/\lambda)$; reason: the inequality uses only $p\in(\bar p,1]$; the page's case is an instance
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, p.ec19

import Mathlib
import Definitions.Def_DevContest_leaderRace
import Definitions.Def_DevContest_firstStageObjective

open scoped NNReal

namespace DevContest

/-- Khorasani, Körpeoğlu, Krishnan, *Dynamic Development Contests*, author manuscript, p.ec19: at a
belief `p ∈ (p̄, 1]`, whatever the rival's first-stage effort `y`,
`V_{1,p} = p V_{1,1} + (1-p) V_{1,0} ≤ p ½(R̄-c/λ) + (1-p)(R̄-c/λ) < c/λ`. Consequently an agent with
no success facing such continuation payoffs at all dates optimally quits: every effort has a
nonpositive value in (EC.39), and zero effort has value `0`. -/
theorem belief_above_pbar_quits {lam c Rbar : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hlow : 2 * c / lam < Rbar) (hhigh : Rbar < 3 * c / lam) :
    (∀ (s : ℝ≥0) (y : ℝ≥0 → ℝ), Measurable y → (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) →
      ∀ p, pBar lam c Rbar < p → p ≤ 1 →
        p * bothValue lam c Rbar s + (1 - p) * leaderValue lam c Rbar y s ≤
          p * (1 / 2 * (Rbar - c / lam)) + (1 - p) * (Rbar - c / lam) ∧
        p * (1 / 2 * (Rbar - c / lam)) + (1 - p) * (Rbar - c / lam) < c / lam) ∧
    ∀ {V1 q x1 x0 φ : ℝ → ℝ}, IsEffort q → IsEffort x1 → IsEffort x0 → IsEffort φ →
      (∀ τ, 0 ≤ τ → ∃ (y : ℝ≥0 → ℝ) (p : ℝ), Measurable y ∧ (∀ t, y t ∈ Set.Icc (0 : ℝ) 1) ∧
        pBar lam c Rbar < p ∧ p ≤ 1 ∧
        V1 τ = p * bothValue lam c Rbar τ.toNNReal +
          (1 - p) * leaderValue lam c Rbar y τ.toNNReal) →
      ∀ t, 0 ≤ t →
        firstStageObjective lam c V1 q x1 x0 φ (fun _ => 0) t = 0 ∧
        ∀ x, IsEffort x → firstStageObjective lam c V1 q x1 x0 φ x t ≤ 0 := by sorry

end DevContest
