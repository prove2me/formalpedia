-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_inv
-- name    : BookProof.ChapterA3.toC_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:18:22.285416+00:00
-- url     : https://prove2.me/theorems/0f0e9166-69d6-4af0-8d71-b1b38b7b4d3a
-- title:
--   `BookProof.ChapterA3.toC_inv` (M : Matrix (Fin 4) (Fin 4) ℝ) : toC M⁻¹ = (toC M)⁻¹
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.toC_inv` (M : Matrix (Fin 4) (Fin 4) ℝ) : toC M⁻¹ = (toC M)⁻¹
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_inv`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.toC_inv
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_inv (M : Matrix (Fin 4) (Fin 4) ℝ) : toC M⁻¹ = (toC M)⁻¹ := by sorry
