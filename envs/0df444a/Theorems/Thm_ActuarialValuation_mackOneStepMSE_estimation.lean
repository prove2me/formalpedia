-- Prove2me | Theorems.Thm_ActuarialValuation_mackOneStepMSE_estimation
-- name    : ActuarialValuation.mackOneStepMSE_estimation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:38.737124+00:00
-- url     : https://prove2.me/theorems/d3328c39-46d0-4a37-a012-bbd819a4d0f2
-- title:
--   Process error, estimation error and reserve variance: mackOneStepMSE_estimation
-- statement:
--   Estimation-only prediction variance has no process component. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   MSE(0,e)=e
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackOneStepMSE

namespace ActuarialValuation

theorem mackOneStepMSE_estimation (e : ℝ) : mackOneStepMSE 0 e = e := by sorry

end ActuarialValuation
