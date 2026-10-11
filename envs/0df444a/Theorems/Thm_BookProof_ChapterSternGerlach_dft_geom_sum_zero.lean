-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_dft_geom_sum_zero
-- name    : BookProof.ChapterSternGerlach.dft_geom_sum_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:45:57.587544+00:00
-- url     : https://prove2.me/theorems/787c8fa2-6037-49b4-b808-df48a551cc29
-- title:
--   `BookProof.ChapterSternGerlach.dft_geom_sum_zero` (n : ℕ) (w : ℂ) (hw : w ≠ 1) (hwn : w ^ n = 1) : ∑ i ∈ Finset.range n, w ^ i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.dft_geom_sum_zero` (n : ℕ) (w : ℂ) (hw : w ≠ 1) (hwn : w ^ n = 1) : ∑ i ∈ Finset.range n, w ^ i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.dft_geom_sum_zero`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.dft_geom_sum_zero
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.dft_geom_sum_zero (n : ℕ) (w : ℂ) (hw : w ≠ 1) (hwn : w ^ n = 1) :
    ∑ i ∈ Finset.range n, w ^ i = 0 := by sorry
