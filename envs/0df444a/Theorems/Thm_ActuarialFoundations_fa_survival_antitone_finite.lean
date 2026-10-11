-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_survival_antitone_finite
-- name    : ActuarialFoundations.fa_survival_antitone_finite
-- status  : Open
-- author  : @WillR
-- created : 2026-10-11T06:48:14.529981+00:00
-- url     : https://prove2.me/theorems/77253782-6810-4f79-8690-3b8e35c415fa
-- title:
--   Cohort probability extensions: survival antitone finite
-- statement:
--   Finite-horizon survival lies between zero and one and cannot increase as duration advances. The claim is restricted to ages within the finite cohort boundary.
-- source:
--   S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., Chapter 3 (life-table survival and mortality); Wiley https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782521 Original-derived finite-cohort Lean statement; this exact theorem wording is not attributed to the text.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faFiniteCohortValid
import Definitions.Def_actuarial_faSurvival

namespace ActuarialFoundations

theorem fa_survival_antitone_finite (l : ℕ → ℝ) (ω x t u : ℕ) (h : faFiniteCohortValid l ω) (hp : 0 < l x) (ht : x+t+u ≤ ω) : 0 ≤ faSurvival l x (t+u) ∧ faSurvival l x (t+u) ≤ faSurvival l x t ∧ faSurvival l x t ≤ 1 := by sorry

end ActuarialFoundations
