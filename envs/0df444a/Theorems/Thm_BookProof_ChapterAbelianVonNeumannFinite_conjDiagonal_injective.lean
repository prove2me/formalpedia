-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianVonNeumannFinite_conjDiagonal_injective
-- name    : BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:30.340294+00:00
-- url     : https://prove2.me/theorems/b09d7ed4-87e0-4449-b466-fab902a41f87
-- title:
--   `BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective` (U : Matrix.unitaryGroup n ℂ) : Function.Injective (conjDiagonal U)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianVonNeumannFinite`.
--
--   `BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective` (U : Matrix.unitaryGroup n ℂ) : Function.Injective (conjDiagonal U)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective`.

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.AbelianDiagonal
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterAbelianVonNeumannFinite.conjDiagonal_injective (U : Matrix.unitaryGroup n ℂ) :
    Function.Injective (conjDiagonal U) := by sorry
