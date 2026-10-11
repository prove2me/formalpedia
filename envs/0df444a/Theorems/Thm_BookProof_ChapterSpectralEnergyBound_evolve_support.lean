-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_evolve_support
-- name    : BookProof.ChapterSpectralEnergyBound.evolve_support
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:20.493589+00:00
-- url     : https://prove2.me/theorems/db5d06be-735e-4390-a145-399c8aaf1eea
-- title:
--   `BookProof.ChapterSpectralEnergyBound.evolve_support` (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) (h : evolve f t v i ≠ 0) : v i ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.evolve_support` (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n) (h : evolve f t v i ≠ 0) : v i ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.evolve_support`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.evolve_support
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.evolve_support (f : n → ℝ) (t : ℝ) (v : EuclideanSpace ℂ n) (i : n)
    (h : evolve f t v i ≠ 0) : v i ≠ 0 := by sorry
