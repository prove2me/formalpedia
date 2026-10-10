-- Prove2me | Theorems.Thm_ActuarialValuation_mackSquaredResidual_zero
-- name    : ActuarialValuation.mackSquaredResidual_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:28:08.800564+00:00
-- url     : https://prove2.me/theorems/81a94468-eaad-4da3-9528-8d254ea03fd3
-- title:
--   Residual dispersion and one-step uncertainty: mackSquaredResidual_zero
-- statement:
--   Perfect fitted development contributes no squared residual. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e(C,C)^2=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual

namespace ActuarialValuation

theorem mackSquaredResidual_zero (actual : ℝ) : mackSquaredResidual actual actual = 0 := by sorry

end ActuarialValuation
