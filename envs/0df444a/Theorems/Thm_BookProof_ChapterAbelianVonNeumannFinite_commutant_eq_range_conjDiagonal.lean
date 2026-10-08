-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianVonNeumannFinite_commutant_eq_range_conjDiagonal
-- name    : BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:49.681597+00:00
-- url     : https://prove2.me/theorems/918df34e-570d-42e4-8a7e-416ebec54520
-- title:
--   `BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal` {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdist : Function.Injective hA.eigenvalues) : {M : Matrix n n ℂ |
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianVonNeumannFinite`.
--
--   `BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal` {A : Matrix n n ℂ} (hA : A.IsHermitian) (hdist : Function.Injective hA.eigenvalues) : {M : Matrix n n ℂ | M * A = A * M} = Set.range (conjDiagonal hA.eigenvectorUnitary)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal`.

-- Generated from ChapterAbelianVonNeumannFinite.lean — theorem BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal
import Mathlib
import Definitions.Def_ChapterAbelianVonNeumannFinite
open BookProof.ChapterAbelianVonNeumannFinite


open Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdist : Function.Injective hA.eigenvalues) :
    {M : Matrix n n ℂ | M * A = A * M} = Set.range (conjDiagonal hA.eigenvectorUnitary) := by sorry
