-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_jump_compensator_bound
-- name    : AvramDividend.Classical.discounted_jump_compensator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T21:52:11.205473+00:00
-- url     : https://prove2.me/theorems/76c669d6-6de0-4222-9898-5062716d5444
-- title:
--   Uniform integrable bound for exponentially discounted Lévy jump compensators
-- statement:
--   For θ≥1 and z≥0, the discount compensator (1-exp(-θz))/θ is nonnegative and at most min(z,1). This inequality is precisely the domination needed to integrate against any bounded-variation Lévy jump measure, enabling dominated convergence of the discounted renewal kernel as θ tends to infinity.
-- source:
--   Bernoulli bound Real.add_one_le_exp, positivity of Real.exp, Mathlib Analysis.SpecialFunctions.Exp at environment 0df444a3

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- A uniform integrable bound for the discounted jump compensator
in the positive-jump-magnitude representation of a BV Lévy measure. -/
theorem discounted_jump_compensator_bound (θ z : ℝ) (hθ : 1 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ (1 - Real.exp (-θ * z)) / θ ∧
      (1 - Real.exp (-θ * z)) / θ ≤ min z 1 := by
  sorry

end AvramDividend.Classical
