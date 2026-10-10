-- Prove2me | Theorems.Thm_ActuarialValuation_clReserve_zero_paid
-- name    : ActuarialValuation.clReserve_zero_paid
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:04.557677+00:00
-- url     : https://prove2.me/theorems/2788ce15-149a-447c-b392-0d250a1f02d9
-- title:
--   Development to ultimate and outstanding reserve: clReserve_zero_paid
-- statement:
--   The chain-ladder reserve is zero for zero observed paid claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R(0,F)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clReserve

namespace ActuarialValuation

theorem clReserve_zero_paid (f : ℝ) : clReserve 0 f = 0 := by sorry

end ActuarialValuation
