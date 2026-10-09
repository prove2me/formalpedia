-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilonC_antihom
-- name    : BookProof.ChapterA3.upsilonC_antihom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:48:49.736539+00:00
-- url     : https://prove2.me/theorems/9a6326d0-1cb3-4fb1-82b7-e684319309de
-- title:
--   `BookProof.ChapterA3.upsilonC_antihom` (T U : Matrix (Fin 2) (Fin 2) ℂ) : UpsilonC (T * U) = UpsilonC U * UpsilonC T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilonC_antihom` (T U : Matrix (Fin 2) (Fin 2) ℂ) : UpsilonC (T * U) = UpsilonC U * UpsilonC T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilonC_antihom`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilonC_antihom
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilonC_antihom (T U : Matrix (Fin 2) (Fin 2) ℂ) :
    UpsilonC (T * U) = UpsilonC U * UpsilonC T := by sorry
