-- Prove2me | Theorems.Thm_ActuarialValuation_mackProjection_unit
-- name    : ActuarialValuation.mackProjection_unit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:27:31.269363+00:00
-- url     : https://prove2.me/theorems/302cd97f-0b55-4064-a6c6-c72576237aad
-- title:
--   Development factors and volume-weighted exposure: mackProjection_unit
-- statement:
--   Full development requires no additional projected claim amount. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \widehat C(C,1)=C
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProjection

namespace ActuarialValuation

theorem mackProjection_unit (c : ℝ) : mackProjection c 1 = c := by sorry

end ActuarialValuation
