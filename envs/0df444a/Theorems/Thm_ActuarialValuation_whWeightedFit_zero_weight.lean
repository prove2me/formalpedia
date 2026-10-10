-- Prove2me | Theorems.Thm_ActuarialValuation_whWeightedFit_zero_weight
-- name    : ActuarialValuation.whWeightedFit_zero_weight
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:02.793999+00:00
-- url     : https://prove2.me/theorems/09d19aff-1439-4040-9905-15fd6cdb5d73
-- title:
--   Observed crude rates and exposure-weighted fitting: whWeightedFit_zero_weight
-- statement:
--   An observation carrying no credibility weight does not influence fit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   w=0\Rightarrow F_x=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit

namespace ActuarialValuation

theorem whWeightedFit_zero_weight (g q : ℝ) : whWeightedFit 0 g q = 0 := by sorry

end ActuarialValuation
