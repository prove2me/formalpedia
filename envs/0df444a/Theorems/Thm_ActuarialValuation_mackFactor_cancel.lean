-- Prove2me | Theorems.Thm_ActuarialValuation_mackFactor_cancel
-- name    : ActuarialValuation.mackFactor_cancel
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:26:47.374526+00:00
-- url     : https://prove2.me/theorems/9551f287-d232-4fb2-add4-5c16c7ddedb4
-- title:
--   Development factors and volume-weighted exposure: mackFactor_cancel
-- statement:
--   The factor calibrates exactly to selected observed adjacent development. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f_jD_j=N_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor

namespace ActuarialValuation

theorem mackFactor_cancel (c : ℕ → ℕ → ℝ) (m j : ℕ) (h : mackDenominator c m j ≠ 0) : mackFactor c m j * mackDenominator c m j = mackNumerator c m j := by sorry

end ActuarialValuation
