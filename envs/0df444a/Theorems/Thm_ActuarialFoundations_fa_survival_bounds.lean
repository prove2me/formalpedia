-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_survival_bounds
-- name    : ActuarialFoundations.fa_survival_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:36:08.125991+00:00
-- url     : https://prove2.me/theorems/c64e886a-b852-4b78-b374-a1c94a745d27
-- title:
--   Survival bounds
-- statement:
--   Prove unit-interval conditional survival bounds for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. Survivor benefits are valued on beginning-year anniversaries, with zero-lives boundary treatment. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 to 5, https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521. Original derived formulation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faFiniteCohortValid
import Definitions.Def_actuarial_faSurvival

namespace ActuarialFoundations

theorem fa_survival_bounds (l : ℕ → ℝ) (ω x n : ℕ) (h : faFiniteCohortValid l ω) (hx : x < ω) (hp : 0 < l x) (hn : x+n ≤ ω) : 0 ≤ faSurvival l x n ∧ faSurvival l x n ≤ 1 := by sorry

end ActuarialFoundations
