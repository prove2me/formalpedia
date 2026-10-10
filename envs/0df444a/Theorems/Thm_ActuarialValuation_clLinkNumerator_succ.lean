-- Prove2me | Theorems.Thm_ActuarialValuation_clLinkNumerator_succ
-- name    : ActuarialValuation.clLinkNumerator_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:26:06.298671+00:00
-- url     : https://prove2.me/theorems/f838fc23-2f51-4cb8-9d38-f75958443316
-- title:
--   Cumulative triangles and selected development factors: clLinkNumerator_succ
-- statement:
--   An additional origin cohort contributes one next-age claim observation. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N_{m+1}=N_m+C_{m,j+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator

namespace ActuarialValuation

theorem clLinkNumerator_succ (p : ℕ → ℕ → ℝ) (m j : ℕ) : clLinkNumerator p (m+1) j = clLinkNumerator p m j + p m (j+1) := by sorry

end ActuarialValuation
