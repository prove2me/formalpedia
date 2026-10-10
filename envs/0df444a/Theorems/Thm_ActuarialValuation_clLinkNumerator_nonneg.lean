-- Prove2me | Theorems.Thm_ActuarialValuation_clLinkNumerator_nonneg
-- name    : ActuarialValuation.clLinkNumerator_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:27:29.939982+00:00
-- url     : https://prove2.me/theorems/1b3d5a19-cb77-4b69-8476-00e1e01a1e48
-- title:
--   Cumulative triangles and selected development factors: clLinkNumerator_nonneg
-- statement:
--   The volume-weighted next-age numerator is nonnegative for nonnegative paid claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   N_j\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator

namespace ActuarialValuation

theorem clLinkNumerator_nonneg (p : ℕ → ℕ → ℝ) (m j : ℕ) (h : ∀ i ∈ Finset.range m, 0 ≤ p i (j+1)) : 0 ≤ clLinkNumerator p m j := by sorry

end ActuarialValuation
