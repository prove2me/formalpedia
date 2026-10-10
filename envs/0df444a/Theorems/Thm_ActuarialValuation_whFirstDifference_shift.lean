-- Prove2me | Theorems.Thm_ActuarialValuation_whFirstDifference_shift
-- name    : ActuarialValuation.whFirstDifference_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:15.5575+00:00
-- url     : https://prove2.me/theorems/94d5ac57-0bf0-44ef-8baf-a62e2608e479
-- title:
--   First and second finite difference smoothness: whFirstDifference_shift
-- statement:
--   Level shifts do not change adjacent mortality increments. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta(g+c)=\Delta g
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference
import Definitions.Def_actuarial_whShiftedCurve

namespace ActuarialValuation

theorem whFirstDifference_shift (g : ℕ → ℝ) (i : ℕ) (s : ℝ) : whFirstDifference (fun j => whShiftedCurve g s j) i = whFirstDifference g i := by sorry

end ActuarialValuation
