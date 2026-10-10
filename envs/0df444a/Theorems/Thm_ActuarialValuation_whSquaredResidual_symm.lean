-- Prove2me | Theorems.Thm_ActuarialValuation_whSquaredResidual_symm
-- name    : ActuarialValuation.whSquaredResidual_symm
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:14:49.120795+00:00
-- url     : https://prove2.me/theorems/6c8a725d-8afe-416b-aa96-a080acc0855f
-- title:
--   Observed crude rates and exposure-weighted fitting: whSquaredResidual_symm
-- statement:
--   Exchanging crude and graduated levels does not change squared error. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (g-q)^2=(q-g)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSquaredResidual

namespace ActuarialValuation

theorem whSquaredResidual_symm (g q : ℝ) : whSquaredResidual g q = whSquaredResidual q g := by sorry

end ActuarialValuation
