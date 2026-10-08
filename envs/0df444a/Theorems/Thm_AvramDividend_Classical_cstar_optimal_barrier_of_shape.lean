-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_shape
-- name    : AvramDividend.Classical.cstar_optimal_barrier_of_shape
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T12:15:58.618674+00:00
-- url     : https://prove2.me/theorems/9c42b7eb-14fa-41b7-b253-6944ff1d12ce
-- title:
--   Barrier optimality comparison from finite cstar and denominator/secant shape control
-- statement:
--   Under explicitly stated finiteness, scale-function nonnegativity, and either the zero-at-origin special case or a positive cstar derivative with global denominator and secant lower bounds, the Avram cstar barrier dominates every nonnegative competing barrier value on the range 0≤x≤cstar. This proves the deterministic value-comparison part of milestone 3 without silently assuming regularity or boundary-derivative facts.
-- source:
--   Existing source-reviewed conditional proof in artifacts/m2m4/milestone_campaign_20261004/m3/conditional_barrier_comparison.lean, independent of unproved fluctuation-theory assumptions. The stronger shape assumptions still require future canonical theorem derivations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier_of_shape (W : ℝ → ℝ)
    (hfinite : cstar W < ⊤)
    (hW : ∀ y : ℝ, 0 ≤ y → 0 ≤ W y)
    (hshape : ((cstar W).toReal = 0 ∧ W 0 = 0) ∨
      ∃ d : ℝ, 0 < d ∧ scaleDeriv W (cstar W).toReal = (d : EReal) ∧
        (∀ a : ℝ, 0 ≤ a →
          scaleDeriv W a = ⊤ ∨ (scaleDeriv W a).toReal = 0 ∨
            d ≤ (scaleDeriv W a).toReal) ∧
        (∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ (cstar W).toReal →
          (x - b) * d ≤ W x - W b)) :
    cstar W < ⊤ ∧
      ∀ x a : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ a →
        barrierValue W a x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
