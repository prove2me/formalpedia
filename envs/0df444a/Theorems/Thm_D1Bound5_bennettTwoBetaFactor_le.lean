-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoBetaFactor_le
-- name    : D1Bound5.bennettTwoBetaFactor_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:47.52078+00:00
-- url     : https://prove2.me/theorems/4d9df885-d823-4852-92d7-229baeb5bba5
-- title:
--   Bennett Two Beta Factor le
-- statement:
--   Uniform quantitative bound on the exact normalized beta factor, for all orders.
-- source:
--   D1Bound5/BennettTwoBetaBound.lean, lines 104-114, SHA-256 6be0ec4b4373f2704cbfdc6beb52a3796d8063f1c67fa2c91242af5752323182. Project: https://github.com/tomislav-math/d1-bound5-lean

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


















theorem _root_.D1Bound5.bennettTwoBetaFactor_le (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoBetaFactor k ≤ 27 / 64 := by sorry



end D1Bound5
end
