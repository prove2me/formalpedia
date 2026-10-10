-- Prove2me | Theorems.Thm_ActuarialValuation_clPaidFraction_cancel
-- name    : ActuarialValuation.clPaidFraction_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:55.104231+00:00
-- url     : https://prove2.me/theorems/6d89bc69-0474-4eea-9fed-698912647443
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clPaidFraction_cancel
-- statement:
--   The fraction-developed and ultimate development factor are multiplicative inverses. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   wF=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidFraction

namespace ActuarialValuation

theorem clPaidFraction_cancel (f : ℝ) (h : f ≠ 0) : clPaidFraction f * f = 1 := by sorry

end ActuarialValuation
