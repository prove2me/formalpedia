-- Prove2me | Theorems.Thm_ActuarialValuation_whSecondRoughness_nonneg
-- name    : ActuarialValuation.whSecondRoughness_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:50.59997+00:00
-- url     : https://prove2.me/theorems/60bcb1c8-03c6-4ada-8ee2-65ba12c250b3
-- title:
--   First and second finite difference smoothness: whSecondRoughness_nonneg
-- statement:
--   Finite squared second differences yield nonnegative curvature roughness. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_2\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness

namespace ActuarialValuation

theorem whSecondRoughness_nonneg (g : ℕ → ℝ) (n : ℕ) : 0 ≤ whSecondRoughness g n := by sorry

end ActuarialValuation
