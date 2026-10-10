-- Prove2me | Theorems.Thm_ActuarialValuation_mackEstimationVariance_nonneg
-- name    : ActuarialValuation.mackEstimationVariance_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:31:07.627052+00:00
-- url     : https://prove2.me/theorems/61bd027c-702e-466f-b145-565dac5a13a4
-- title:
--   Process error, estimation error and reserve variance: mackEstimationVariance_nonneg
-- statement:
--   Parameter uncertainty is nonnegative with positive observed exposure. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   s\ge0,D>0\Rightarrow v_e\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackEstimationVariance

namespace ActuarialValuation

theorem mackEstimationVariance_nonneg (s c d : ℝ) (hs : 0 ≤ s) (hd : 0 < d) : 0 ≤ mackEstimationVariance s c d := by sorry

end ActuarialValuation
