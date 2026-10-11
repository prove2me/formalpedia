-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_hasDerivAt_evolve
-- name    : BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:56:42.233618+00:00
-- url     : https://prove2.me/theorems/d93f3cc6-4fcf-448d-a03a-e87342c9526c
-- title:
--   `BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve` (f : n → ℝ) (v : EuclideanSpace ℂ n) (t : ℝ) : HasDerivAt (fun s : ℝ => evolve f s v) (-Complex.I • diagOp f (evolve f t v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve` (f : n → ℝ) (v : EuclideanSpace ℂ n) (t : ℝ) : HasDerivAt (fun s : ℝ => evolve f s v) (-Complex.I • diagOp f (evolve f t v)) t
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.hasDerivAt_evolve (f : n → ℝ) (v : EuclideanSpace ℂ n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => evolve f s v)
      (-Complex.I • diagOp f (evolve f t v)) t := by sorry
