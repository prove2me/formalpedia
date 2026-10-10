-- Prove2me | Theorems.Thm_ActuarialValuation_clFactorToUltimate_single
-- name    : ActuarialValuation.clFactorToUltimate_single
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:35.552288+00:00
-- url     : https://prove2.me/theorems/895cfd4c-591d-4909-a8c7-d2000e5f17cb
-- title:
--   Development to ultimate and outstanding reserve: clFactorToUltimate_single
-- statement:
--   A single development interval has exactly its one-step link factor. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_{j,1}=f_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate

namespace ActuarialValuation

theorem clFactorToUltimate_single (f : ℕ → ℝ) (j : ℕ) : clFactorToUltimate f j 1 = f j := by sorry

end ActuarialValuation
