-- Prove2me | Theorems.Thm_ActuarialValuation_whSecondDifference_linear
-- name    : ActuarialValuation.whSecondDifference_linear
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:05.69776+00:00
-- url     : https://prove2.me/theorems/b18589bb-aa8b-4f8e-a24c-533d33b3c437
-- title:
--   First and second finite difference smoothness: whSecondDifference_linear
-- statement:
--   An affine age trend has exactly zero second finite difference. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta^2(a+bi)=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whLinearCurve

namespace ActuarialValuation

theorem whSecondDifference_linear (a b : ℝ) (i : ℕ) : whSecondDifference (whLinearCurve a b) i = 0 := by sorry

end ActuarialValuation
