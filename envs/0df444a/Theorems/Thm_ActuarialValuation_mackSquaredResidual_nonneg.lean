-- Prove2me | Theorems.Thm_ActuarialValuation_mackSquaredResidual_nonneg
-- name    : ActuarialValuation.mackSquaredResidual_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:27:55.202505+00:00
-- url     : https://prove2.me/theorems/bb509de3-07bc-4387-9dea-438c7333b24b
-- title:
--   Residual dispersion and one-step uncertainty: mackSquaredResidual_nonneg
-- statement:
--   Squared cumulative claims residual is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e^2\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual

namespace ActuarialValuation

theorem mackSquaredResidual_nonneg (actual predicted : ℝ) : 0 ≤ mackSquaredResidual actual predicted := by sorry

end ActuarialValuation
