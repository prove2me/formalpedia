-- Prove2me | Theorems.Thm_ActuarialValuation_clPaidIncrement_reconcile
-- name    : ActuarialValuation.clPaidIncrement_reconcile
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:25:11.90298+00:00
-- url     : https://prove2.me/theorems/1e779ebd-547c-41c5-91df-2b39bae52a06
-- title:
--   Cumulative triangles and selected development factors: clPaidIncrement_reconcile
-- statement:
--   Paid movement reconciles to the next cumulative paid amount. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_j+I=C_{j+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement

namespace ActuarialValuation

theorem clPaidIncrement_reconcile (p : ℕ → ℕ → ℝ) (i j : ℕ) : p i j + clPaidIncrement p i j = p i (j+1) := by sorry

end ActuarialValuation
