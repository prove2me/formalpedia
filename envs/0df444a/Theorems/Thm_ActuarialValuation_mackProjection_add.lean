-- Prove2me | Theorems.Thm_ActuarialValuation_mackProjection_add
-- name    : ActuarialValuation.mackProjection_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:27:42.247407+00:00
-- url     : https://prove2.me/theorems/235f678f-e606-45dc-a142-891be728703e
-- title:
--   Development factors and volume-weighted exposure: mackProjection_add
-- statement:
--   One common factor distributes over aggregated claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \widehat C(C+D)=\widehat C(C)+\widehat C(D)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 213. Thomas Mack (1993), Distribution-free Calculation of the Standard Error of Chain Ladder Reserve Estimates, ASTIN Bulletin 23(2), pp. 213-225, https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf; Thomas Mack (1999), The Standard Error of Chain Ladder Reserve Estimates: Recursive Calculation and Inclusion of a Tail Factor, https://www.casact.org/sites/default/files/database/astin_vol29no2_361.pdf. Parent topic: Mack claims reserving uncertainty, finite conditional development factor moments, process variance and estimation uncertainty. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/astin_vol23no2_213.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProjection

namespace ActuarialValuation

theorem mackProjection_add (c d f : ℝ) : mackProjection (c+d) f = mackProjection c f + mackProjection d f := by sorry

end ActuarialValuation
