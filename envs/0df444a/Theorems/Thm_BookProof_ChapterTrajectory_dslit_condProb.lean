-- Prove2me | Theorems.Thm_BookProof_ChapterTrajectory_dslit_condProb
-- name    : BookProof.ChapterTrajectory.dslit_condProb
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:14:08.142892+00:00
-- url     : https://prove2.me/theorems/d2d8af2b-c35c-4a8e-9155-195aa67cdca4
-- title:
--   `BookProof.ChapterTrajectory.dslit_condProb` (f a : Fin 2) : condProb H H psi0 f a = 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTrajectory`.
--
--   `BookProof.ChapterTrajectory.dslit_condProb` (f a : Fin 2) : condProb H H psi0 f a = 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterTrajectory.dslit_condProb`.

-- Generated from ChapterTrajectory.lean — theorem BookProof.ChapterTrajectory.dslit_condProb
import Mathlib
import Definitions.Def_ChapterTrajectory
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterTrajectory


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterTrajectory.dslit_condProb (f a : Fin 2) : condProb H H psi0 f a = 1 / 2 := by sorry
