-- Prove2me | Theorems.Thm_ActuarialValuation_mackReserveVariance_fundamental
-- name    : ActuarialValuation.mackReserveVariance_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:45.217586+00:00
-- url     : https://prove2.me/theorems/d4127d51-e4ee-4105-ae2f-a85eaa6799bc
-- title:
--   Process error, estimation error and reserve variance: mackReserveVariance_fundamental
-- statement:
--   The capstone combines observed factor calibration, separate nonnegative process and estimation variance terms, and claims reserve reconciliation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   fD=N,\;v_p,v_e,MSE\ge0,\;C+R=U
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor
import Definitions.Def_actuarial_mackProjection
import Definitions.Def_actuarial_mackProcessVariance
import Definitions.Def_actuarial_mackEstimationVariance
import Definitions.Def_actuarial_mackOneStepMSE
import Definitions.Def_actuarial_mackReserve

namespace ActuarialValuation

theorem mackReserveVariance_fundamental (c : ℕ → ℕ → ℝ) (m j : ℕ) (hD : 0 < mackDenominator c m j) (current sigma2 : ℝ) (hc : 0 ≤ current) (hs : 0 ≤ sigma2) : (mackFactor c m j * mackDenominator c m j = mackNumerator c m j) ∧ (0 ≤ mackProcessVariance sigma2 current) ∧ (0 ≤ mackEstimationVariance sigma2 current (mackDenominator c m j)) ∧ (0 ≤ mackOneStepMSE (mackProcessVariance sigma2 current) (mackEstimationVariance sigma2 current (mackDenominator c m j))) ∧ (current + mackReserve (mackProjection current (mackFactor c m j)) current = mackProjection current (mackFactor c m j)) := by sorry

end ActuarialValuation
