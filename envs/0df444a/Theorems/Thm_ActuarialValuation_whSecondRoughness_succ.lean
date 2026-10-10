-- Prove2me | Theorems.Thm_ActuarialValuation_whSecondRoughness_succ
-- name    : ActuarialValuation.whSecondRoughness_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:21.825122+00:00
-- url     : https://prove2.me/theorems/bd99d9a4-4ba1-4df3-a769-1a41e1332bc8
-- title:
--   First and second finite difference smoothness: whSecondRoughness_succ
-- statement:
--   Adding one age comparison adds exactly one curvature penalty term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_{2,n+1}=S_{2,n}+(\Delta^2g_n)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference
import Definitions.Def_actuarial_whSecondRoughness

namespace ActuarialValuation

theorem whSecondRoughness_succ (g : ℕ → ℝ) (n : ℕ) : whSecondRoughness g (n+1) = whSecondRoughness g n + (whSecondDifference g n)^2 := by sorry

end ActuarialValuation
