-- Prove2me | Theorems.Thm_BookProof_ChapterA3_sigmaC_mul_transpose
-- name    : BookProof.ChapterA3.sigmaC_mul_transpose
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:54:03.658111+00:00
-- url     : https://prove2.me/theorems/6c51ba6c-7df0-4d2f-9f7b-f471a2e2d323
-- title:
--   `BookProof.ChapterA3.sigmaC_mul_transpose` : SigmaC * SigmaCᵀ = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.sigmaC_mul_transpose` : SigmaC * SigmaCᵀ = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.sigmaC_mul_transpose`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.sigmaC_mul_transpose
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.sigmaC_mul_transpose :
    SigmaC * SigmaCᵀ = (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
