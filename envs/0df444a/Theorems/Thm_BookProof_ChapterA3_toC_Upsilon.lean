-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_Upsilon
-- name    : BookProof.ChapterA3.toC_Upsilon
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:49:21.204314+00:00
-- url     : https://prove2.me/theorems/0dbb86a5-2755-4762-83e1-c2099ed61ca4
-- title:
--   `BookProof.ChapterA3.toC_Upsilon` (T : Matrix (Fin 2) (Fin 2) ℂ) : toC (Upsilon T) = UpsilonC T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.toC_Upsilon` (T : Matrix (Fin 2) (Fin 2) ℂ) : toC (Upsilon T) = UpsilonC T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_Upsilon`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.toC_Upsilon
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_Upsilon (T : Matrix (Fin 2) (Fin 2) ℂ) :
    toC (Upsilon T) = UpsilonC T := by sorry
