-- Prove2me | Theorems.Thm_ActuarialValuation_mackDenominator_succ
-- name    : ActuarialValuation.mackDenominator_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:53:31.895649+00:00
-- url     : https://prove2.me/theorems/3042a6b4-52ee-47cb-bc3c-beb04b0661db
-- title:
--   Development factors and volume-weighted exposure: mackDenominator_succ
-- statement:
--   One extra origin year contributes its adjacent earlier loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   D_{m+1}=D_m+C_{m,j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackDenominator

namespace ActuarialValuation

theorem mackDenominator_succ (c : ℕ → ℕ → ℝ) (m j : ℕ) : mackDenominator c (m+1) j = mackDenominator c m j + c m j := by sorry

end ActuarialValuation
