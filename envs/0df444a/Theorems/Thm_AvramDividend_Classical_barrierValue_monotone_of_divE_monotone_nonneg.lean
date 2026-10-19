-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_monotone_of_divE_monotone_nonneg
-- name    : AvramDividend.Classical.barrierValue_monotone_of_divE_monotone_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:13:32.824365+00:00
-- url     : https://prove2.me/theorems/e5c96e03-8fc3-4263-9797-492705aacbb2
-- title:
--   Piecewise dividend barrier value is globally monotone from nonnegative increasing scaled W
-- statement:
--   Suppose a finite dividend barrier a is nonnegative, the scaled branch z↦divE(W z)(scaleDeriv W a) is nonnegative on nonnegative arguments and monotone on [0,∞). Then the exact piecewise barrierValue W a is globally nondecreasing on all real reserves: zero on negative capital, the scaled W branch up to a, and affine with slope one above a. This solves the piecewise monotonicity glue needed when bounding negative-jump integrands, without silently presuming derivative-denominator positivity from scale-function hypotheses.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierValue_monotone_of_divE_monotone_nonneg (W : ℝ → ℝ) (a : ℝ)
    (ha : 0 ≤ a)
    (hm : MonotoneOn (fun z : ℝ => divE (W z) (scaleDeriv W a)) (Ici 0))
    (hn : ∀ z : ℝ, 0 ≤ z → 0 ≤ divE (W z) (scaleDeriv W a)) :
    Monotone (barrierValue W a) := by sorry
