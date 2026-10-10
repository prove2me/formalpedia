-- Prove2me | Theorems.Thm_ActuarialValuation_clBFUltimate_blend
-- name    : ActuarialValuation.clBFUltimate_blend
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:50:04.204023+00:00
-- url     : https://prove2.me/theorems/b6286b45-a807-4fe7-957b-2a28b1f6ebb5
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFUltimate_blend
-- statement:
--   The BF ultimate equals a development-weighted blend of chain ladder and a priori ultimate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   U_{BF}=wU_{CL}+(1-w)E
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clPaidFraction
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFUltimate

namespace ActuarialValuation

theorem clBFUltimate_blend (c e f : ℝ) (hf : f ≠ 0) : clBFUltimate c e f = clPaidFraction f * clUltimate c f + clUnpaidFraction f * e := by sorry

end ActuarialValuation
