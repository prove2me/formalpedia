-- Prove2me | Theorems.Thm_ActuarialValuation_clPaidIncrement_nonneg
-- name    : ActuarialValuation.clPaidIncrement_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:24:59.820214+00:00
-- url     : https://prove2.me/theorems/8b663422-7afc-463d-b510-f56f89032215
-- title:
--   Cumulative triangles and selected development factors: clPaidIncrement_nonneg
-- statement:
--   Cumulative nondecreasing paid claims imply nonnegative incremental payments. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_{j+1}\ge C_j\Rightarrow I\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement

namespace ActuarialValuation

theorem clPaidIncrement_nonneg (p : ℕ → ℕ → ℝ) (i j : ℕ) (h : p i j ≤ p i (j+1)) : 0 ≤ clPaidIncrement p i j := by sorry

end ActuarialValuation
