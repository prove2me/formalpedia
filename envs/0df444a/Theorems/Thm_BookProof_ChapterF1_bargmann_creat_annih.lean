-- Prove2me | Theorems.Thm_BookProof_ChapterF1_bargmann_creat_annih
-- name    : BookProof.ChapterF1.bargmann_creat_annih
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:46:07.892311+00:00
-- url     : https://prove2.me/theorems/a4fb9a2a-fda5-4c38-aa0a-63092ec0a5e6
-- title:
--   `BookProof.ChapterF1.bargmann_creat_annih` (m n : ℕ) : bargmann (creat (X ^ m)) (X ^ n) = bargmann (X ^ m) (annih (X ^ n))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.bargmann_creat_annih` (m n : ℕ) : bargmann (creat (X ^ m)) (X ^ n) = bargmann (X ^ m) (annih (X ^ n))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.bargmann_creat_annih`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.bargmann_creat_annih
import Mathlib
import Definitions.Def_ChapterF1
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.bargmann_creat_annih (m n : ℕ) :
    bargmann (creat (X ^ m)) (X ^ n) = bargmann (X ^ m) (annih (X ^ n)) := by sorry
