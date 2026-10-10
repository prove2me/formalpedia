-- Prove2me | Theorems.Thm_ActuarialValuation_clLinkDenominator_zero
-- name    : ActuarialValuation.clLinkDenominator_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:25:50.810981+00:00
-- url     : https://prove2.me/theorems/79f2724a-624f-4c0e-8ab2-a09e03c60c2e
-- title:
--   Cumulative triangles and selected development factors: clLinkDenominator_zero
-- statement:
--   Empty origin-year exposure produces a zero link denominator. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{j,0}=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkDenominator

namespace ActuarialValuation

theorem clLinkDenominator_zero (p : ℕ → ℕ → ℝ) (j : ℕ) : clLinkDenominator p 0 j = 0 := by sorry

end ActuarialValuation
