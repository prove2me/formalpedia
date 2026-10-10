-- Prove2me | Theorems.Thm_ActuarialValuation_clUltimate_add
-- name    : ActuarialValuation.clUltimate_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:34:42.762979+00:00
-- url     : https://prove2.me/theorems/d04a7f7f-7c04-46dd-b35a-908faaebfdf7
-- title:
--   Development to ultimate and outstanding reserve: clUltimate_add
-- statement:
--   Development at fixed factor commutes with aggregating current paid claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U(C_1+C_2)=U(C_1)+U(C_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate

namespace ActuarialValuation

theorem clUltimate_add (p q f : ℝ) : clUltimate (p+q) f = clUltimate p f + clUltimate q f := by sorry

end ActuarialValuation
