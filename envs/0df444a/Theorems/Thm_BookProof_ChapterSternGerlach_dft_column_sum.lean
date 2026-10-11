-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_dft_column_sum
-- name    : BookProof.ChapterSternGerlach.dft_column_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:45:53.21139+00:00
-- url     : https://prove2.me/theorems/0f33be3c-08b2-4776-b99e-99099a09e1ae
-- title:
--   `BookProof.ChapterSternGerlach.dft_column_sum` (n : ℕ) (hn : 0 < n) (j : Fin n) : ∑ i, Complex.normSq (dftMatrix n i j) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.dft_column_sum` (n : ℕ) (hn : 0 < n) (j : Fin n) : ∑ i, Complex.normSq (dftMatrix n i j) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.dft_column_sum`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.dft_column_sum
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.dft_column_sum (n : ℕ) (hn : 0 < n) (j : Fin n) :
    ∑ i, Complex.normSq (dftMatrix n i j) = 1 := by sorry
