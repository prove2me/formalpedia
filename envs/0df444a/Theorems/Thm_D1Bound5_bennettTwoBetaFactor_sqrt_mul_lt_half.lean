-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoBetaFactor_sqrt_mul_lt_half
-- name    : D1Bound5.bennettTwoBetaFactor_sqrt_mul_lt_half
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:47:57.8276+00:00
-- url     : https://prove2.me/theorems/5926192b-5337-4880-b96c-4f666c043b5a
-- title:
--   Bennett Two Beta Factor sqrt mul lt half
-- statement:
--   The normalized residual bound is strictly below one half once the exact beta expression has been derived; no estimate of a recurrence is assumed.
-- source:
--   D1Bound5/BennettTwoBetaBound.lean, lines 116-128, SHA-256 6be0ec4b4373f2704cbfdc6beb52a3796d8063f1c67fa2c91242af5752323182. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions

section
namespace D1Bound5




















theorem _root_.D1Bound5.bennettTwoBetaFactor_sqrt_mul_lt_half
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt η * bennettTwoBetaFactor k < 1 / 2 := by sorry

end D1Bound5
end
