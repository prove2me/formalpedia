-- Prove2me | Theorems.Thm_BookProof_ChapterA3_adj2_mul_T
-- name    : BookProof.ChapterA3.adj2_mul_T
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:55:08.788486+00:00
-- url     : https://prove2.me/theorems/394bae5b-3ab9-4368-806c-467759cfba6b
-- title:
--   `BookProof.ChapterA3.adj2_mul_T` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : adj2 T * T = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.adj2_mul_T` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : adj2 T * T = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.adj2_mul_T`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.adj2_mul_T
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.adj2_mul_T (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    adj2 T * T = 1 := by sorry
