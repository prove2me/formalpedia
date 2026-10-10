-- Prove2me | Theorems.Thm_ActuarialValuation_mackScaledResidual_zero
-- name    : ActuarialValuation.mackScaledResidual_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:28:45.348977+00:00
-- url     : https://prove2.me/theorems/f3c085bb-4b97-4424-bdc8-74a050181dd4
-- title:
--   Residual dispersion and one-step uncertainty: mackScaledResidual_zero
-- statement:
--   Exact predicted claims produce zero scaled squared residual. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e=0\Rightarrow z=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual

namespace ActuarialValuation

theorem mackScaledResidual_zero (a e : ℝ) : mackScaledResidual a a e = 0 := by sorry

end ActuarialValuation
