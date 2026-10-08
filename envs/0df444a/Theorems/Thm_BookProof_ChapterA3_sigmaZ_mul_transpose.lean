-- Prove2me | Theorems.Thm_BookProof_ChapterA3_sigmaZ_mul_transpose
-- name    : BookProof.ChapterA3.sigmaZ_mul_transpose
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:54:05.08351+00:00
-- url     : https://prove2.me/theorems/b77a438c-ace3-4394-9b7b-6b244cbf9c02
-- title:
--   `BookProof.ChapterA3.sigmaZ_mul_transpose` : SigmaZ * SigmaZᵀ = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.sigmaZ_mul_transpose` : SigmaZ * SigmaZᵀ = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.sigmaZ_mul_transpose`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.sigmaZ_mul_transpose
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.sigmaZ_mul_transpose :
    SigmaZ * SigmaZᵀ = (2 : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by sorry
