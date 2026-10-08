-- Prove2me | Theorems.Thm_BookProof_ChapterA3_spinor_inv_eq
-- name    : BookProof.ChapterA3.spinor_inv_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:08:34.198665+00:00
-- url     : https://prove2.me/theorems/d7d9c5b9-6b90-4de3-8861-2ce66f6349f4
-- title:
--   `BookProof.ChapterA3.spinor_inv_eq` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : (Spinor T)⁻¹ = SpinorInv T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3i`.
--
--   `BookProof.ChapterA3.spinor_inv_eq` (T : Matrix (Fin 2) (Fin 2) ℂ) (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) : (Spinor T)⁻¹ = SpinorInv T
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.spinor_inv_eq`.

-- Generated from ChapterA3i.lean — theorem BookProof.ChapterA3.spinor_inv_eq
import Mathlib
import Definitions.Def_ChapterA3i
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.spinor_inv_eq (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hdet : T 0 0 * T 1 1 - T 0 1 * T 1 0 = 1) :
    (Spinor T)⁻¹ = SpinorInv T := by sorry
