-- Prove2me | Theorems.Thm_BookProof_ChapterSternGerlach_exists_uniform_unitary
-- name    : BookProof.ChapterSternGerlach.exists_uniform_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:46:15.979366+00:00
-- url     : https://prove2.me/theorems/5e30d914-2f1d-4857-894c-9a657e9f0a12
-- title:
--   `BookProof.ChapterSternGerlach.exists_uniform_unitary` (n : ℕ) (hn : 0 < n) : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ i j : Fin n, Complex.normSq (U i j) = 1 / n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSternGerlach`.
--
--   `BookProof.ChapterSternGerlach.exists_uniform_unitary` (n : ℕ) (hn : 0 < n) : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ i j : Fin n, Complex.normSq (U i j) = 1 / n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSternGerlach.exists_uniform_unitary`.

-- Generated from ChapterSternGerlach.lean — theorem BookProof.ChapterSternGerlach.exists_uniform_unitary
import Mathlib
import Definitions.Def_ChapterSternGerlach
open BookProof.ChapterSternGerlach



open Complex Matrix Finset

theorem BookProof.ChapterSternGerlach.exists_uniform_unitary (n : ℕ) (hn : 0 < n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ i j : Fin n, Complex.normSq (U i j) = 1 / n := by sorry
