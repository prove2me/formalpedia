-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_dft_mem_unitaryGroup
-- name    : BookProof.ChapterSternGerlach.dft_mem_unitaryGroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:27.679071+00:00
-- url     : https://prove2.me/theorems/66abd364-f49e-4412-87a1-c5566019a784
-- title:
--   `BookProof.ChapterSternGerlach.dft_mem_unitaryGroup` (n : ℕ) (hn : 0 < n) : dftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.dft_mem_unitaryGroup` (n : ℕ) (hn : 0 < n) : dftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.dft_mem_unitaryGroup`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.dft_mem_unitaryGroup
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.dft_mem_unitaryGroup (n : ℕ) (hn : 0 < n) :
    dftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by sorry
