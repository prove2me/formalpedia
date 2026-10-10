-- Prove2me | Theorems.Thm_ActuarialValuation_mackSigmaSquared_zero
-- name    : ActuarialValuation.mackSigmaSquared_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:30:17.654985+00:00
-- url     : https://prove2.me/theorems/51c7d9d9-8431-4e4a-976b-33aefc8154a4
-- title:
--   Residual dispersion and one-step uncertainty: mackSigmaSquared_zero
-- statement:
--   No residual variation means zero estimated variance. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V=0\Rightarrow\hat\sigma^2=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSigmaSquared

namespace ActuarialValuation

theorem mackSigmaSquared_zero (df : ℝ) : mackSigmaSquared 0 df = 0 := by sorry

end ActuarialValuation
