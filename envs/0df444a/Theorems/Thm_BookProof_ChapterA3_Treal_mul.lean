-- Prove2me | Theorems.Thm_BookProof_ChapterA3_Treal_mul
-- name    : BookProof.ChapterA3.Treal_mul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:54:14.553614+00:00
-- url     : https://prove2.me/theorems/e81b62cd-d60a-4320-bcc9-ee58c65dd6ae
-- title:
--   `BookProof.ChapterA3.Treal_mul` (A B : Matrix (Fin 2) (Fin 2) ℂ) : Treal (A * B) = Treal A * Treal B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.Treal_mul` (A B : Matrix (Fin 2) (Fin 2) ℂ) : Treal (A * B) = Treal A * Treal B
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.Treal_mul`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.Treal_mul
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.Treal_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Treal (A * B) = Treal A * Treal B := by sorry
