-- Prove2me | Theorems.Thm_ActuarialValuation_clUltimate_zero
-- name    : ActuarialValuation.clUltimate_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:29:46.48505+00:00
-- url     : https://prove2.me/theorems/3dace064-b24c-4aec-bbe6-e1efce5fe5a9
-- title:
--   Development to ultimate and outstanding reserve: clUltimate_zero
-- statement:
--   No latest paid claims produce no modelled ultimate under multiplicative development. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U(0,F)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate

namespace ActuarialValuation

theorem clUltimate_zero (f : ℝ) : clUltimate 0 f = 0 := by sorry

end ActuarialValuation
