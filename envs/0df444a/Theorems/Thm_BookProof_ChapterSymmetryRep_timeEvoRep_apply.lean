-- Prove2me | Theorems.Thm_BookProof_ChapterSymmetryRep_timeEvoRep_apply
-- name    : BookProof.ChapterSymmetryRep.timeEvoRep_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:13:25.931494+00:00
-- url     : https://prove2.me/theorems/8a49d703-2a00-401b-9de8-5fa0be2c1ba8
-- title:
--   `BookProof.ChapterSymmetryRep.timeEvoRep_apply` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : (timeEvoRep H hH (Multiplicative.ofAdd t) : Matrix n n ℂ) = timeEvo H t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSymmetryRep`.
--
--   `BookProof.ChapterSymmetryRep.timeEvoRep_apply` (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) : (timeEvoRep H hH (Multiplicative.ofAdd t) : Matrix n n ℂ) = timeEvo H t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSymmetryRep.timeEvoRep_apply`.

-- Generated from ChapterSymmetryRep.lean — theorem BookProof.ChapterSymmetryRep.timeEvoRep_apply
import Mathlib
import Definitions.Def_ChapterSymmetryRep
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative
open BookProof.ChapterSymmetryRep


open scoped Matrix


open BookProof.ChapterConservative

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterSymmetryRep.timeEvoRep_apply (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvoRep H hH (Multiplicative.ofAdd t) : Matrix n n ℂ) = timeEvo H t := by sorry
