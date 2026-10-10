-- Prove2me | Theorems.Thm_ActuarialValuation_clReserve_factor_one
-- name    : ActuarialValuation.clReserve_factor_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:34:56.803652+00:00
-- url     : https://prove2.me/theorems/98b064a4-7e98-4b5c-9fcd-4832f094c38f
-- title:
--   Development to ultimate and outstanding reserve: clReserve_factor_one
-- statement:
--   Fully developed claims carry zero chain-ladder unpaid reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R(C,1)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clReserve

namespace ActuarialValuation

theorem clReserve_factor_one (p : ℝ) : clReserve p 1 = 0 := by sorry

end ActuarialValuation
