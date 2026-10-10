-- Prove2me | Theorems.Thm_ActuarialValuation_clFactorToUltimate_zero
-- name    : ActuarialValuation.clFactorToUltimate_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:28:58.810438+00:00
-- url     : https://prove2.me/theorems/bff1586a-d6f8-4295-976b-e319d801d8a7
-- title:
--   Development to ultimate and outstanding reserve: clFactorToUltimate_zero
-- statement:
--   Fully developed claim years require no additional factor. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_{j,0}=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate

namespace ActuarialValuation

theorem clFactorToUltimate_zero (f : ℕ → ℝ) (j : ℕ) : clFactorToUltimate f j 0 = 1 := by sorry

end ActuarialValuation
