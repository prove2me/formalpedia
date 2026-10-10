-- Prove2me | Theorems.Thm_ActuarialValuation_whFitPenalty_succ
-- name    : ActuarialValuation.whFitPenalty_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:51.708435+00:00
-- url     : https://prove2.me/theorems/d9244d8a-1391-4ecf-a8c9-986844676f7f
-- title:
--   Observed crude rates and exposure-weighted fitting: whFitPenalty_succ
-- statement:
--   Each extra observed age adds one nonnegative weighted error term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_{n+1}=F_n+w_n(g_n-q_n)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit
import Definitions.Def_actuarial_whFitPenalty

namespace ActuarialValuation

theorem whFitPenalty_succ (w g q : ℕ → ℝ) (n : ℕ) : whFitPenalty w g q (n+1) = whFitPenalty w g q n + whWeightedFit (w n) (g n) (q n) := by sorry

end ActuarialValuation
