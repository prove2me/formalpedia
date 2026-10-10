-- Prove2me | Theorems.Thm_ActuarialValuation_clUltimate_reserve_balance
-- name    : ActuarialValuation.clUltimate_reserve_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:33.550162+00:00
-- url     : https://prove2.me/theorems/2913e0ad-a917-4624-82e6-866221b8122f
-- title:
--   Development to ultimate and outstanding reserve: clUltimate_reserve_balance
-- statement:
--   The ultimate estimate is reconciled exactly to paid claims and outstanding reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C+R=U
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clReserve

namespace ActuarialValuation

theorem clUltimate_reserve_balance (p f : ℝ) : p + clReserve p f = clUltimate p f := by sorry

end ActuarialValuation
