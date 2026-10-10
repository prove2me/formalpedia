-- Prove2me | Theorems.Thm_ActuarialValuation_whFitPenalty_zero
-- name    : ActuarialValuation.whFitPenalty_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:35.527983+00:00
-- url     : https://prove2.me/theorems/98fc0604-5ae0-4cfe-a549-e3aef72c607f
-- title:
--   Observed crude rates and exposure-weighted fitting: whFitPenalty_zero
-- statement:
--   A cohort with no observed ages has no fitting loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_0=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFitPenalty

namespace ActuarialValuation

theorem whFitPenalty_zero (w g q : ℕ → ℝ) : whFitPenalty w g q 0 = 0 := by sorry

end ActuarialValuation
