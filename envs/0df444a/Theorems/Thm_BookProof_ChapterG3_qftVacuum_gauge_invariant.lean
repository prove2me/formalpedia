-- Prove2me | Theorems.Thm_BookProof_ChapterG3_qftVacuum_gauge_invariant
-- name    : BookProof.ChapterG3.qftVacuum_gauge_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T11:36:24.435447+00:00
-- url     : https://prove2.me/theorems/e16afbbb-598f-4743-b6b6-a8c7f30c3eef
-- title:
--   `BookProof.ChapterG3.qftVacuum_gauge_invariant` (k : ℕ) (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) : (qftVacuum k).map L = qftVacuum k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.qftVacuum_gauge_invariant` (k : ℕ) (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) : (qftVacuum k).map L = qftVacuum k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.qftVacuum_gauge_invariant`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.qftVacuum_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.qftVacuum_gauge_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (qftVacuum k).map L = qftVacuum k := by sorry
