-- Prove2me | Theorems.Thm_ActuarialValuation_clPriorUltimate_nonneg
-- name    : ActuarialValuation.clPriorUltimate_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:37:44.178838+00:00
-- url     : https://prove2.me/theorems/e2dd12ea-dd65-4772-a283-8991722fb487
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clPriorUltimate_nonneg
-- statement:
--   Nonnegative earned premium and loss ratio give a nonnegative a priori claims ultimate. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P,\ell\ge0\Rightarrow E\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPriorUltimate

namespace ActuarialValuation

theorem clPriorUltimate_nonneg (p l : ℝ) (hp : 0 ≤ p) (hl : 0 ≤ l) : 0 ≤ clPriorUltimate p l := by sorry

end ActuarialValuation
