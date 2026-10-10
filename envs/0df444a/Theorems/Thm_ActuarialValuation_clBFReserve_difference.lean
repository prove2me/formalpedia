-- Prove2me | Theorems.Thm_ActuarialValuation_clBFReserve_difference
-- name    : ActuarialValuation.clBFReserve_difference
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:50:30.818251+00:00
-- url     : https://prove2.me/theorems/c517b8e8-037f-4068-a1c7-37759bbc0034
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFReserve_difference
-- statement:
--   The gap between BF and CL is the unpaid fraction times the gap between prior and chain-ladder ultimate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{BF}-U_{CL}=(1-w)(E-U_{CL})
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFUltimate

namespace ActuarialValuation

theorem clBFReserve_difference (c e f : ℝ) (hf : f ≠ 0) : clBFUltimate c e f - clUltimate c f = clUnpaidFraction f * (e - clUltimate c f) := by sorry

end ActuarialValuation
