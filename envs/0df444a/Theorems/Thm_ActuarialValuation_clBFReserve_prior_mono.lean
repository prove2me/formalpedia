-- Prove2me | Theorems.Thm_ActuarialValuation_clBFReserve_prior_mono
-- name    : ActuarialValuation.clBFReserve_prior_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:51:17.083325+00:00
-- url     : https://prove2.me/theorems/9a684758-3fed-49ff-b0d0-3df275c36a64
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFReserve_prior_mono
-- statement:
--   A greater a priori claims expectation raises expected future liability when development factor is at least one. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E_1\le E_2\Rightarrow R_{BF,1}\le R_{BF,2}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve

namespace ActuarialValuation

theorem clBFReserve_prior_mono (e1 e2 f : ℝ) (he : e1 ≤ e2) (hf : 1 ≤ f) : clBFReserve e1 f ≤ clBFReserve e2 f := by sorry

end ActuarialValuation
