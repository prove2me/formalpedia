-- Prove2me | Theorems.Thm_ActuarialValuation_whObjectiveTwo_lambda_mono
-- name    : ActuarialValuation.whObjectiveTwo_lambda_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:20:24.464344+00:00
-- url     : https://prove2.me/theorems/7a6cbef4-5be4-4598-8fdc-bb1879a543da
-- title:
--   Composite graduation objective and invariance: whObjectiveTwo_lambda_mono
-- statement:
--   Curvature penalty increases with its nonnegative smoothing coefficient. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \lambda_1\le\lambda_2\Rightarrow J_2(\lambda_1)\le J_2(\lambda_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveTwo

namespace ActuarialValuation

theorem whObjectiveTwo_lambda_mono (fit smooth l1 l2 : ℝ) (hs : 0 ≤ smooth) (h : l1 ≤ l2) : whObjectiveTwo fit smooth l1 ≤ whObjectiveTwo fit smooth l2 := by sorry

end ActuarialValuation
