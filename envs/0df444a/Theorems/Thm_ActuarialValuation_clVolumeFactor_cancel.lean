-- Prove2me | Theorems.Thm_ActuarialValuation_clVolumeFactor_cancel
-- name    : ActuarialValuation.clVolumeFactor_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:28:08.106994+00:00
-- url     : https://prove2.me/theorems/1d4ce8a2-f407-4810-8a47-7e6f073b5b45
-- title:
--   Cumulative triangles and selected development factors: clVolumeFactor_cancel
-- statement:
--   The volume-weighted link factor reconstructs the next development-age total. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f_jD_j=N_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator
import Definitions.Def_actuarial_clVolumeFactor

namespace ActuarialValuation

theorem clVolumeFactor_cancel (p : ℕ → ℕ → ℝ) (m j : ℕ) (h : clLinkDenominator p m j ≠ 0) : clVolumeFactor p m j * clLinkDenominator p m j = clLinkNumerator p m j := by sorry

end ActuarialValuation
