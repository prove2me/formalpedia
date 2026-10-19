-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_deriv_evolve_le
-- name    : BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:57:16.835446+00:00
-- url     : https://prove2.me/theorems/30b9a5c3-a334-4ac1-a80c-ea3fb8e68a1c
-- title:
--   `BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (t : ℝ) : ‖-Complex.I • diagOp f...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (t : ℝ) : ‖-Complex.I • diagOp f (evolve f t v)‖ ≤ E * ‖v‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.norm_deriv_evolve_le (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n)
    (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (t : ℝ) :
    ‖-Complex.I • diagOp f (evolve f t v)‖ ≤ E * ‖v‖ := by sorry
