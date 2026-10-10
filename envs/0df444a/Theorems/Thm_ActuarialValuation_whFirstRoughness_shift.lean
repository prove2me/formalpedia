-- Prove2me | Theorems.Thm_ActuarialValuation_whFirstRoughness_shift
-- name    : ActuarialValuation.whFirstRoughness_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:38.336286+00:00
-- url     : https://prove2.me/theorems/25a0943c-c86b-4b79-a506-1915ccf1c564
-- title:
--   Composite graduation objective and invariance: whFirstRoughness_shift
-- statement:
--   Uniform rate level shifts preserve first order roughness exactly. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_1(g+c)=S_1(g)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstRoughness
import Definitions.Def_actuarial_whShiftedCurve

namespace ActuarialValuation

theorem whFirstRoughness_shift (g : ℕ → ℝ) (n : ℕ) (s : ℝ) : whFirstRoughness (fun i => whShiftedCurve g s i) n = whFirstRoughness g n := by sorry

end ActuarialValuation
