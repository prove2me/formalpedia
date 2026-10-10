-- Prove2me | Theorems.Thm_ActuarialValuation_whFitPenalty_exact
-- name    : ActuarialValuation.whFitPenalty_exact
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:26.819672+00:00
-- url     : https://prove2.me/theorems/79aac8d7-1997-4a9c-b257-859f8fa6e204
-- title:
--   Observed crude rates and exposure-weighted fitting: whFitPenalty_exact
-- statement:
--   No data fidelity loss arises when graduated values exactly equal crude rates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_i=q_i\Rightarrow F=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFitPenalty

namespace ActuarialValuation

theorem whFitPenalty_exact (w g : ℕ → ℝ) (n : ℕ) : whFitPenalty w g g n = 0 := by sorry

end ActuarialValuation
