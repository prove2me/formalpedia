-- Prove2me | Theorems.Thm_BookProof_ChapterB4_pure_state_satisfies_P1
-- name    : BookProof.ChapterB4.pure_state_satisfies_P1
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:51:51.417997+00:00
-- url     : https://prove2.me/theorems/61f069cc-0a8d-4f00-8aa1-58449962339d
-- title:
--   `BookProof.ChapterB4.pure_state_satisfies_P1` : ∃ ρ, IsPureState ρ ∧ Matrix.trace (ρ * P1) = 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterB4`.
--
--   `BookProof.ChapterB4.pure_state_satisfies_P1` : ∃ ρ, IsPureState ρ ∧ Matrix.trace (ρ * P1) = 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterB4.pure_state_satisfies_P1`.

-- Generated from ChapterB4.lean — theorem BookProof.ChapterB4.pure_state_satisfies_P1
import Mathlib
import Definitions.Def_ChapterB4
open BookProof.ChapterB4



open Matrix

noncomputable section

theorem BookProof.ChapterB4.pure_state_satisfies_P1 :
    ∃ ρ, IsPureState ρ ∧ Matrix.trace (ρ * P1) = 1 / 2 := by sorry
