-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilonC_Qc
-- name    : BookProof.ChapterA3.upsilonC_Qc
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:49:42.075593+00:00
-- url     : https://prove2.me/theorems/a6d12583-7e76-423e-963e-209c72072424
-- title:
--   `BookProof.ChapterA3.upsilonC_Qc` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℂ) : Qc (fun μ => ∑ ν, UpsilonC T μ ν * x ν) = Qc x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilonC_Qc` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℂ) : Qc (fun μ => ∑ ν, UpsilonC T μ ν * x ν) = Qc x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilonC_Qc`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilonC_Qc
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilonC_Qc (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) (x : Fin 4 → ℂ) :
    Qc (fun μ => ∑ ν, UpsilonC T μ ν * x ν) = Qc x := by sorry
