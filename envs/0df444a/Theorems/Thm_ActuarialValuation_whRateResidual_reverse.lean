-- Prove2me | Theorems.Thm_ActuarialValuation_whRateResidual_reverse
-- name    : ActuarialValuation.whRateResidual_reverse
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:14:06.682232+00:00
-- url     : https://prove2.me/theorems/e55db723-ac37-4493-bac4-2353d783ebf6
-- title:
--   Observed crude rates and exposure-weighted fitting: whRateResidual_reverse
-- statement:
--   Reversing the subtraction order negates the graduation residual. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e(g,q)=-e(q,g)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whRateResidual

namespace ActuarialValuation

theorem whRateResidual_reverse (g q : ℝ) : whRateResidual g q = - whRateResidual q g := by sorry

end ActuarialValuation
