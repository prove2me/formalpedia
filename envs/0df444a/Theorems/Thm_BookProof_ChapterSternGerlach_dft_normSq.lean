-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_dft_normSq
-- name    : BookProof.ChapterSternGerlach.dft_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:14.904333+00:00
-- url     : https://prove2.me/theorems/e53aa902-2f23-4188-87bc-36d0ae60a9fe
-- title:
--   `BookProof.ChapterSternGerlach.dft_normSq` (n : ℕ) (hn : 0 < n) (i j : Fin n) : Complex.normSq (dftMatrix n i j) = 1 / n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.dft_normSq` (n : ℕ) (hn : 0 < n) (i j : Fin n) : Complex.normSq (dftMatrix n i j) = 1 / n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.dft_normSq`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.dft_normSq
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.dft_normSq (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    Complex.normSq (dftMatrix n i j) = 1 / n := by sorry
