-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilonC_real
-- name    : BookProof.ChapterA3.upsilonC_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:49:09.300188+00:00
-- url     : https://prove2.me/theorems/287b1eb1-ccb3-4894-b799-800ff3dead16
-- title:
--   `BookProof.ChapterA3.upsilonC_real` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 4) : conj (UpsilonC T μ ν) = UpsilonC T μ ν
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilonC_real` (T : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 4) : conj (UpsilonC T μ ν) = UpsilonC T μ ν
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilonC_real`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilonC_real
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilonC_real (T : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : Fin 4) :
    conj (UpsilonC T μ ν) = UpsilonC T μ ν := by sorry
