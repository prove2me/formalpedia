-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_norm_evolve_apply
-- name    : BookProof.ChapterSpectralEnergyBound.norm_evolve_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:50:54.473494+00:00
-- url     : https://prove2.me/theorems/8541bacf-d185-44ff-ad6b-256f73494023
-- title:
--   `BookProof.ChapterSpectralEnergyBound.norm_evolve_apply` (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) : ‖evolve f t v i‖ = ‖v i‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.norm_evolve_apply` (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) : ‖evolve f t v i‖ = ‖v i‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.norm_evolve_apply`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.norm_evolve_apply
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.norm_evolve_apply (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    ‖evolve f t v i‖ = ‖v i‖ := by sorry
