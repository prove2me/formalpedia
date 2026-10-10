-- Prove2me | Theorems.Thm_ActuarialValuation_whObjectiveOne_nonneg
-- name    : ActuarialValuation.whObjectiveOne_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:19:18.436606+00:00
-- url     : https://prove2.me/theorems/dc832089-b1ce-406a-8490-c41c2dabb7d5
-- title:
--   Composite graduation objective and invariance: whObjectiveOne_nonneg
-- statement:
--   Positive fit and smoothing weights make the objective nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F,S,\lambda\ge0\Rightarrow J_1\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whObjectiveOne

namespace ActuarialValuation

theorem whObjectiveOne_nonneg (fit smooth lambda : ℝ) (hf : 0 ≤ fit) (hs : 0 ≤ smooth) (hl : 0 ≤ lambda) : 0 ≤ whObjectiveOne fit smooth lambda := by sorry

end ActuarialValuation
