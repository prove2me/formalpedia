-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_normalised_death_mass
-- name    : ActuarialFoundations.fa_normalised_death_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:36:26.787314+00:00
-- url     : https://prove2.me/theorems/78576a2a-54b6-43ad-be61-f1c670a3f342
-- title:
--   Normalised death mass
-- statement:
--   Prove a complete conditional death probability distribution for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. The claim is valued at the end of the death year, and terminal-age endpoints are disjoint. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDeaths

namespace ActuarialFoundations

theorem fa_normalised_death_mass (l : ℕ → ℝ) (ω x : ℕ) (hx : x ≤ ω) (hω : l ω = 0) (hp : 0 < l x) : (∑ k ∈ Finset.range (ω-x), faDeaths l (x+k) / l x) = 1 := by sorry

end ActuarialFoundations
