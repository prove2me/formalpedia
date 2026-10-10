-- Prove2me | Theorems.Thm_ActuarialValuation_mackNumerator_succ
-- name    : ActuarialValuation.mackNumerator_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:49:52.909398+00:00
-- url     : https://prove2.me/theorems/758a44ba-605c-4a12-aee8-df2efa9f62ac
-- title:
--   Development factors and volume-weighted exposure: mackNumerator_succ
-- statement:
--   One extra observed origin year contributes one more adjacent later loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N_{m+1}=N_m+C_{m,j+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator

namespace ActuarialValuation

theorem mackNumerator_succ (c : ℕ → ℕ → ℝ) (m j : ℕ) : mackNumerator c (m+1) j = mackNumerator c m j + c m (j+1) := by sorry

end ActuarialValuation
