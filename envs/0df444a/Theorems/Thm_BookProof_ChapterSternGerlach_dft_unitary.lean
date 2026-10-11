-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_dft_unitary
-- name    : BookProof.ChapterSternGerlach.dft_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:19.416964+00:00
-- url     : https://prove2.me/theorems/847d0944-5dc1-4067-a533-6b0a864cc52f
-- title:
--   `BookProof.ChapterSternGerlach.dft_unitary` (n : ℕ) (hn : 0 < n) : dftMatrix n * star (dftMatrix n) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.dft_unitary` (n : ℕ) (hn : 0 < n) : dftMatrix n * star (dftMatrix n) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.dft_unitary`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.dft_unitary
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.dft_unitary (n : ℕ) (hn : 0 < n) :
    dftMatrix n * star (dftMatrix n) = 1 := by sorry
