-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoBetaFactor_succ
-- name    : D1Bound5.bennettTwoBetaFactor_succ
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:16.594983+00:00
-- url     : https://prove2.me/theorems/6410c5ee-326c-44e8-a363-81b57dd4b60a
-- title:
--   Bennett Two Beta Factor succ
-- statement:
--   The actual Gamma sequence obeys the rational recurrence used in the paper.
-- source:
--   D1Bound5/BennettTwoBetaBound.lean, lines 48-80, SHA-256 6be0ec4b4373f2704cbfdc6beb52a3796d8063f1c67fa2c91242af5752323182. Project: https://github.com/tomislav-math/d1-bound5-lean

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












theorem _root_.D1Bound5.bennettTwoBetaFactor_succ (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoBetaFactor (k + 1) = bennettTwoBetaFactor k *
      (((27 / 4 : ℝ) * ((k : ℝ) + 3 / 2) * (2 * (k : ℝ) - 1 / 2) *
        (2 * (k : ℝ) + 1 / 2)) /
          ((3 * (k : ℝ) + 1) * (3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3))) := by sorry









end D1Bound5
end
