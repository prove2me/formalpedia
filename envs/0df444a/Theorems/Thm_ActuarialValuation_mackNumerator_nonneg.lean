-- Prove2me | Theorems.Thm_ActuarialValuation_mackNumerator_nonneg
-- name    : ActuarialValuation.mackNumerator_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:53:52.651992+00:00
-- url     : https://prove2.me/theorems/b6262b3e-3dd4-4a71-ad18-1ea1f176d031
-- title:
--   Development factors and volume-weighted exposure: mackNumerator_nonneg
-- statement:
--   Nonnegative cumulative amounts give a nonnegative next-age sum. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C_{i,j+1}\ge0\Rightarrow N\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator

namespace ActuarialValuation

theorem mackNumerator_nonneg (c : ℕ → ℕ → ℝ) (m j : ℕ) (h : ∀ i ∈ Finset.range m, 0 ≤ c i (j+1)) : 0 ≤ mackNumerator c m j := by sorry

end ActuarialValuation
