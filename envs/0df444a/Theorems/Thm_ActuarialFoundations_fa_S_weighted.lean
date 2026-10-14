-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_S_weighted
-- name    : ActuarialFoundations.fa_S_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T23:33:56.836905+00:00
-- url     : https://prove2.me/theorems/eecc258a-876a-4f8b-b948-947534ddbbf8
-- title:
--   S weighted
-- statement:
--   Prove the closed finite double-sum increasing-benefit weighting for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. Survivor benefits are valued on beginning-year anniversaries, with zero-lives boundary treatment. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faDiscountedLives
import Definitions.Def_actuarial_faS

namespace ActuarialFoundations

theorem fa_S_weighted (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : faS l v ω x = (∑ k ∈ Finset.range (ω-x), ((k+1 : ℕ) : ℝ) * faDiscountedLives l v (x+k)) := by sorry

end ActuarialFoundations
