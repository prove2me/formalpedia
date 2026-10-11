-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_fundamental_identity
-- name    : ActuarialFoundations.fa_fundamental_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T23:33:37.544003+00:00
-- url     : https://prove2.me/theorems/810e94bf-3a59-4485-b995-7ceb8e70ef02
-- title:
--   Fundamental identity
-- statement:
--   Prove the finite whole-life valuation capital identity for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. Survivor benefits are valued on beginning-year anniversaries, with zero-lives boundary treatment. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faAnnuityOriginal
import Definitions.Def_actuarial_faAssuranceOriginal

namespace ActuarialFoundations

theorem fa_fundamental_identity (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) (hx : x < ω) (hl : l x ≠ 0) (hω : l ω = 0) : faAssuranceOriginal l v ω x + (1-v)*faAnnuityOriginal l v ω x = 1 := by sorry

end ActuarialFoundations
