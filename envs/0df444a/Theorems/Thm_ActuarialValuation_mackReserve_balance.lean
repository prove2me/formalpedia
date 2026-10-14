-- Prove2me | Theorems.Thm_ActuarialValuation_mackReserve_balance
-- name    : ActuarialValuation.mackReserve_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:31:53.118214+00:00
-- url     : https://prove2.me/theorems/c3b02685-5b14-490e-97e1-4d77690c6a45
-- title:
--   Process error, estimation error and reserve variance: mackReserve_balance
-- statement:
--   Outstanding reserve reconciles predicted ultimate to paid claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   C+R=U
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackReserve

namespace ActuarialValuation

theorem mackReserve_balance (projected current : ℝ) : current + mackReserve projected current = projected := by sorry

end ActuarialValuation
