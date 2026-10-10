-- Prove2me | Theorems.Thm_ActuarialValuation_mackFactor_nonneg
-- name    : ActuarialValuation.mackFactor_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:27:06.396436+00:00
-- url     : https://prove2.me/theorems/2703622b-6d5d-401d-bc34-fdebb3fa84f3
-- title:
--   Development factors and volume-weighted exposure: mackFactor_nonneg
-- statement:
--   Development-factor estimation preserves nonnegativity with valid exposures. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N\ge0,D>0\Rightarrow f\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor

namespace ActuarialValuation

theorem mackFactor_nonneg (c : ℕ → ℕ → ℝ) (m j : ℕ) (hn : 0 ≤ mackNumerator c m j) (hd : 0 < mackDenominator c m j) : 0 ≤ mackFactor c m j := by sorry

end ActuarialValuation
