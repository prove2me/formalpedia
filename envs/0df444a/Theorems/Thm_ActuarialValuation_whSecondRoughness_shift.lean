-- Prove2me | Theorems.Thm_ActuarialValuation_whSecondRoughness_shift
-- name    : ActuarialValuation.whSecondRoughness_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:49.96632+00:00
-- url     : https://prove2.me/theorems/0d43aaec-2186-4451-8f8c-fafdba7ee2d6
-- title:
--   Composite graduation objective and invariance: whSecondRoughness_shift
-- statement:
--   Uniform rate shifts preserve second order curvature penalties. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_2(g+c)=S_2(g)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whShiftedCurve

namespace ActuarialValuation

theorem whSecondRoughness_shift (g : ℕ → ℝ) (n : ℕ) (s : ℝ) : whSecondRoughness (fun i => whShiftedCurve g s i) n = whSecondRoughness g n := by sorry

end ActuarialValuation
