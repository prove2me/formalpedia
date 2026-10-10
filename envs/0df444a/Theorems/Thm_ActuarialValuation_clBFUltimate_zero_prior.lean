-- Prove2me | Theorems.Thm_ActuarialValuation_clBFUltimate_zero_prior
-- name    : ActuarialValuation.clBFUltimate_zero_prior
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:49:42.972982+00:00
-- url     : https://prove2.me/theorems/d291ef6d-42dc-47de-9818-aaf0728af1e0
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clBFUltimate_zero_prior
-- statement:
--   A zero external prior leaves only already emerged paid claims. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E=0\Rightarrow U_{BF}=C
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFUltimate

namespace ActuarialValuation

theorem clBFUltimate_zero_prior (c f : ℝ) : clBFUltimate c 0 f = c := by sorry

end ActuarialValuation
