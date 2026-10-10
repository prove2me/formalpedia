-- Prove2me | Theorems.Thm_ActuarialValuation_clPaidFraction_nonneg
-- name    : ActuarialValuation.clPaidFraction_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:38:34.491981+00:00
-- url     : https://prove2.me/theorems/d5069b52-195f-4be1-a0bf-da1e7503b20f
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clPaidFraction_nonneg
-- statement:
--   The developed fraction is nonnegative for positive age-to-ultimate development. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F>0\Rightarrow w\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidFraction

namespace ActuarialValuation

theorem clPaidFraction_nonneg (f : ℝ) (h : 0 < f) : 0 ≤ clPaidFraction f := by sorry

end ActuarialValuation
