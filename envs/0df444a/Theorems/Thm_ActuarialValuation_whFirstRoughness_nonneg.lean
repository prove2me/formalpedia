-- Prove2me | Theorems.Thm_ActuarialValuation_whFirstRoughness_nonneg
-- name    : ActuarialValuation.whFirstRoughness_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:34.805157+00:00
-- url     : https://prove2.me/theorems/8241d324-1311-4ccf-a97d-b2254ee6284b
-- title:
--   First and second finite difference smoothness: whFirstRoughness_nonneg
-- statement:
--   Finite squared first differences yield nonnegative roughness. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_1\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstRoughness

namespace ActuarialValuation

theorem whFirstRoughness_nonneg (g : ℕ → ℝ) (n : ℕ) : 0 ≤ whFirstRoughness g n := by sorry

end ActuarialValuation
