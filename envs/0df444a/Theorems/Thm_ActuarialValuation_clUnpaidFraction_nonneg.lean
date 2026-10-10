-- Prove2me | Theorems.Thm_ActuarialValuation_clUnpaidFraction_nonneg
-- name    : ActuarialValuation.clUnpaidFraction_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:41:01.892847+00:00
-- url     : https://prove2.me/theorems/dbf30d75-9251-472b-b99d-2b94bed7690f
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clUnpaidFraction_nonneg
-- statement:
--   Age-to-ultimate factors at least one imply nonnegative future emergence. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F\ge1\Rightarrow u\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUnpaidFraction

namespace ActuarialValuation

theorem clUnpaidFraction_nonneg (f : ℝ) (h : 1 ≤ f) : 0 ≤ clUnpaidFraction f := by sorry

end ActuarialValuation
