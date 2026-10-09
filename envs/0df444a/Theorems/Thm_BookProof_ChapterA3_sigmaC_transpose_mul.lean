-- Prove2me | Theorems.Thm_BookProof_ChapterA3_sigmaC_transpose_mul
-- name    : BookProof.ChapterA3.sigmaC_transpose_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:56:54.719765+00:00
-- url     : https://prove2.me/theorems/c00766ed-8149-44a6-970c-79e7d15b5827
-- title:
--   `BookProof.ChapterA3.sigmaC_transpose_mul` : SigmaCᵀ * SigmaC = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.sigmaC_transpose_mul` : SigmaCᵀ * SigmaC = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.sigmaC_transpose_mul`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.sigmaC_transpose_mul
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.sigmaC_transpose_mul :
    SigmaCᵀ * SigmaC = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
