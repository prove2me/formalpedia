-- Prove2me | Theorems.Thm_ActuarialValuation_mackVarianceNumerator_nonneg
-- name    : ActuarialValuation.mackVarianceNumerator_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:29:40.641875+00:00
-- url     : https://prove2.me/theorems/ce1c6ffb-45f7-40d7-9a67-365e2baf48b1
-- title:
--   Residual dispersion and one-step uncertainty: mackVarianceNumerator_nonneg
-- statement:
--   A finite sum of positive-exposure squared residuals is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_i>0\Rightarrow V\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackVarianceNumerator

namespace ActuarialValuation

theorem mackVarianceNumerator_nonneg (a b e : ℕ → ℝ) (m : ℕ) (h : ∀ i ∈ Finset.range m, 0 < e i) : 0 ≤ mackVarianceNumerator a b e m := by sorry

end ActuarialValuation
