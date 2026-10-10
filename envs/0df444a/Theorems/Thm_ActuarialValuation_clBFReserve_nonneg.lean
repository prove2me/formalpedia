-- Prove2me | Theorems.Thm_ActuarialValuation_clBFReserve_nonneg
-- name    : ActuarialValuation.clBFReserve_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:46:46.070654+00:00
-- url     : https://prove2.me/theorems/aa443feb-c81f-43aa-9ab1-8651fb5ec359
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFReserve_nonneg
-- statement:
--   Nonnegative expected losses and remaining emergence yield nonnegative reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E\ge0,F\ge1\Rightarrow R_{BF}\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve

namespace ActuarialValuation

theorem clBFReserve_nonneg (e f : ℝ) (he : 0 ≤ e) (hf : 1 ≤ f) : 0 ≤ clBFReserve e f := by sorry

end ActuarialValuation
