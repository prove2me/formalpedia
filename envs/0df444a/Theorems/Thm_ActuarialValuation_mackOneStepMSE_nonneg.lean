-- Prove2me | Theorems.Thm_ActuarialValuation_mackOneStepMSE_nonneg
-- name    : ActuarialValuation.mackOneStepMSE_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:17.209976+00:00
-- url     : https://prove2.me/theorems/ed5a3e88-2a81-4a86-82b8-ecfb60bef12c
-- title:
--   Process error, estimation error and reserve variance: mackOneStepMSE_nonneg
-- statement:
--   Total mean squared prediction error combines nonnegative contributions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   p,e\ge0\Rightarrow MSE\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackOneStepMSE

namespace ActuarialValuation

theorem mackOneStepMSE_nonneg (p e : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) : 0 ≤ mackOneStepMSE p e := by sorry

end ActuarialValuation
