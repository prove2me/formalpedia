-- Prove2me | Theorems.Thm_ActuarialValuation_clFactorToUltimate_succ
-- name    : ActuarialValuation.clFactorToUltimate_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:11.172081+00:00
-- url     : https://prove2.me/theorems/6a1c97ae-510a-4007-8995-ac5cc2074c82
-- title:
--   Development to ultimate and outstanding reserve: clFactorToUltimate_succ
-- statement:
--   Development-to-ultimate factors append one further age-to-age ratio. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_{j,n+1}=F_{j,n}f_{j+n}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate

namespace ActuarialValuation

theorem clFactorToUltimate_succ (f : ℕ → ℝ) (j n : ℕ) : clFactorToUltimate f j (n+1) = clFactorToUltimate f j n * f (j+n) := by sorry

end ActuarialValuation
