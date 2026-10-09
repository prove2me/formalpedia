-- Prove2me | Theorems.Thm_BookProof_ChapterA3_T_mul_adj2
-- name    : BookProof.ChapterA3.T_mul_adj2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:54:48.15127+00:00
-- url     : https://prove2.me/theorems/3e6b05cc-7e18-4494-82ec-dbed0e62a279
-- title:
--   `BookProof.ChapterA3.T_mul_adj2` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : T * adj2 T = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.T_mul_adj2` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : T * adj2 T = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.T_mul_adj2`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.T_mul_adj2
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.T_mul_adj2 (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    T * adj2 T = 1 := by sorry
