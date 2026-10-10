-- Prove2me | Theorems.Thm_ActuarialValuation_whSecondDifference_shift
-- name    : ActuarialValuation.whSecondDifference_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:29.490301+00:00
-- url     : https://prove2.me/theorems/0d7e3407-f8da-4e88-8a74-6d6924303ee9
-- title:
--   First and second finite difference smoothness: whSecondDifference_shift
-- statement:
--   Curvature penalties are invariant to uniform changes of mortality level. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta^2(g+c)=\Delta^2g
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whShiftedCurve

namespace ActuarialValuation

theorem whSecondDifference_shift (g : ℕ → ℝ) (i : ℕ) (s : ℝ) : whSecondDifference (fun j => whShiftedCurve g s j) i = whSecondDifference g i := by sorry

end ActuarialValuation
