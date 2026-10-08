-- Prove2me | Theorems.Thm_BookProof_ChapterA3_spinorInv_mul_spinor
-- name    : BookProof.ChapterA3.spinorInv_mul_spinor
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:55:59.138835+00:00
-- url     : https://prove2.me/theorems/5bae4446-8372-447e-8230-d8c8b0a979a8
-- title:
--   `BookProof.ChapterA3.spinorInv_mul_spinor` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : SpinorInv T * Spinor T = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.spinorInv_mul_spinor` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : SpinorInv T * Spinor T = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.spinorInv_mul_spinor`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.spinorInv_mul_spinor
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.spinorInv_mul_spinor (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    SpinorInv T * Spinor T = 1 := by sorry
