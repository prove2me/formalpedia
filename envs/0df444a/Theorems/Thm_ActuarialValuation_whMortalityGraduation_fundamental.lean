-- Prove2me | Theorems.Thm_ActuarialValuation_whMortalityGraduation_fundamental
-- name    : ActuarialValuation.whMortalityGraduation_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:21:20.877204+00:00
-- url     : https://prove2.me/theorems/ec03b716-0aae-4c43-8c65-7fb65ec61dd0
-- title:
--   Composite graduation objective and invariance: whMortalityGraduation_fundamental
-- statement:
--   The capstone proves a nonnegative exposure-weighted mortality graduation criterion and exact curvature shift invariance under explicit weighting assumptions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F\ge0,\;S_2\ge0,\;F+\lambda S_2\ge0,\;S_2(g+c)=S_2(g)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFitPenalty
import Definitions.Def_actuarial_whSecondRoughness
import Definitions.Def_actuarial_whObjectiveTwo
import Definitions.Def_actuarial_whShiftedCurve

namespace ActuarialValuation

theorem whMortalityGraduation_fundamental (w g crude : ℕ → ℝ) (n : ℕ) (lambda shift : ℝ) (hw : ∀ i ∈ Finset.range n, 0 ≤ w i) (hl : 0 ≤ lambda) : (0 ≤ whFitPenalty w g crude n) ∧ (0 ≤ whSecondRoughness g n) ∧ (0 ≤ whObjectiveTwo (whFitPenalty w g crude n) (whSecondRoughness g n) lambda) ∧ (whSecondRoughness (fun i => whShiftedCurve g shift i) n = whSecondRoughness g n) := by sorry

end ActuarialValuation
