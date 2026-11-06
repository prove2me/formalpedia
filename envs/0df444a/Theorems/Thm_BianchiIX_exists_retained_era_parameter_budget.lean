-- Prove2me | Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
-- name    : BianchiIX.exists_retained_era_parameter_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:03:51.30167+00:00
-- url     : https://prove2.me/theorems/7bb6cbb9-5114-4e7f-b791-006cdc5b46a9
-- title:
--   One amplitude threshold supplies every retained digit condition
-- statement:
--   Let $\varepsilon>0$, $C\geq0$, $J\in\mathbb N$,
--   $0<\sigma<1$, and $2J\sigma<1$. There exists $B_*\in(0,1)$ such that
--   for every $0<B\leq B_*$, writing $\beta=B^\sigma$, one has
--   $$0<\beta<1/160,\quad B\leq\varepsilon(\beta/2)^{2J},
--   \quad CB<\beta/4.$$
--   Moreover, every $m\in\mathbb N$ with $m+1\leq1/\beta$ satisfies
--   $$2B(m+2-\beta)\leq\varepsilon.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RetainedEraParameters.lean#L9-L58

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.exists_retained_era_parameter_budget {ε C σ : ℝ} {J : ℕ}
    (hε : 0 < ε) (hC : 0 ≤ C) (hσ : 0 < σ) (hσone : σ < 1)
    (hσJ : σ * (2 * J : ℕ) < 1) :
    ∃ Bstar : ℝ, 0 < Bstar ∧ Bstar < 1 ∧ ∀ B ∈ Ioc 0 Bstar,
      let β := B ^ σ
      0 < β ∧ β < 1 / 160 ∧ B ≤ ε * (β / 2) ^ (2 * J) ∧ C * B < β / 4 ∧
      ∀ m : ℕ, (m : ℝ) + 1 ≤ 1 / β → B * (2 * ((m : ℝ) + 2 - β)) ≤ ε := by sorry
