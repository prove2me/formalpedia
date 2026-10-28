-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoBeta_ratio_lt_one
-- name    : D1Bound5.bennettTwoBeta_ratio_lt_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:49.644991+00:00
-- url     : https://prove2.me/theorems/38b03861-6b65-427b-8131-7c365435502e
-- title:
--   Bennett Two Beta ratio lt one
-- statement:
--   The rational recurrence factor is strictly below one at every positive order.
-- source:
--   D1Bound5/BennettTwoBetaBound.lean, lines 82-96, SHA-256 6be0ec4b4373f2704cbfdc6beb52a3796d8063f1c67fa2c91242af5752323182. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5














theorem _root_.D1Bound5.bennettTwoBeta_ratio_lt_one (k : ℕ) (hk : 1 ≤ k) :
    (((27 / 4 : ℝ) * ((k : ℝ) + 3 / 2) * (2 * (k : ℝ) - 1 / 2) *
      (2 * (k : ℝ) + 1 / 2)) /
        ((3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3))) < 1 := by sorry







end D1Bound5
end
