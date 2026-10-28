-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exponential_nnreal_survival_memorylessness
-- name    : AvramDividend.Classical.avram_ws01e_b_exponential_nnreal_survival_memorylessness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:53:49.680195+00:00
-- url     : https://prove2.me/theorems/0d7052c0-760b-4482-a044-3ae3abfab515
-- title:
--   Exponential strict-survival kernel is memoryless for all nonnegative ages
-- statement:
--   For any positive real exponential-clock rate p and all nonnegative stopping age a and additional duration t, the extended-nonnegative strict-survival probability kernel exp(-p(a+t)) equals the product exp(-pt)exp(-pa), with all real exponentials embedded in ENNReal. This exact NNReal/ENNReal interface combines with the genuine Exp(p) tail theorem to discharge the shift hypothesis of the accepted conditional stopped-age clock factor. The proof uses the real exponential addition law, the nonnegative-age casting identity and the pinned ENNReal.ofReal_mul theorem.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

open scoped NNReal ENNReal

/-- The authentic exponential-clock strict-survival kernel is memoryless
for all nonnegative stopping ages and increments. The ENNReal factors are
finite, positive real exponentials; no divergent expectation is involved. -/

theorem AvramDividend.Classical.avram_ws01e_b_exponential_nnreal_survival_memorylessness
    (p : ℝ) (hp : 0 < p) (a t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(p * ((a + t : ℝ≥0) : ℝ)))) =
      ENNReal.ofReal (Real.exp (-(p * (t : ℝ)))) *
        ENNReal.ofReal (Real.exp (-(p * (a : ℝ)))) := by sorry
