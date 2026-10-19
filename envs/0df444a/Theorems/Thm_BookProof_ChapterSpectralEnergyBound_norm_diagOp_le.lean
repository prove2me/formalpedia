-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_diagOp_le
-- name    : BookProof.ChapterSpectralEnergyBound.norm_diagOp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:24.007614+00:00
-- url     : https://prove2.me/theorems/6fe6848f-e55f-4de6-b077-aab0659ae980
-- title:
--   `BookProof.ChapterSpectralEnergyBound.norm_diagOp_le` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) : ‖diagOp f v‖ ≤ E * ‖v‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.norm_diagOp_le` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) : ‖diagOp f v‖ ≤ E * ‖v‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.norm_diagOp_le`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.norm_diagOp_le
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.norm_diagOp_le (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n)
    (h : ∀ i, v i ≠ 0 → |f i| ≤ E) :
    ‖diagOp f v‖ ≤ E * ‖v‖ := by sorry
