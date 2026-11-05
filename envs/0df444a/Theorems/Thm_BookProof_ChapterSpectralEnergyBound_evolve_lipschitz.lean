-- Prove2me | Theorems.Thm_BookProof_ChapterSpectralEnergyBound_evolve_lipschitz
-- name    : BookProof.ChapterSpectralEnergyBound.evolve_lipschitz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T19:56:52.515195+00:00
-- url     : https://prove2.me/theorems/7a47089c-82c7-40e5-9fe1-a72f6cc52384
-- title:
--   `BookProof.ChapterSpectralEnergyBound.evolve_lipschitz` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (s t : ℝ) : ‖evolve f t v - evolve f s...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSpectralEnergyBound`.
--
--   `BookProof.ChapterSpectralEnergyBound.evolve_lipschitz` (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n) (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (s t : ℝ) : ‖evolve f t v - evolve f s v‖ ≤ E * ‖v‖ * |t - s| := by have hderiv : ∀ x ∈ Set.uIcc s t, HasDerivWithinAt (fun r : ℝ => evolve f r v) (-Complex.I • diagOp f (evolve f x v)) (Set.uIcc s t) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSpectralEnergyBound.evolve_lipschitz`.

-- Generated from ChapterSpectralEnergyBound.lean — theorem BookProof.ChapterSpectralEnergyBound.evolve_lipschitz
import Mathlib
import Definitions.Def_ChapterSpectralEnergyBound
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBornMeasure
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterBornMeasure
open BookProof.ChapterSpectralEnergyBound



variable {n : Type*} [Fintype n]

theorem BookProof.ChapterSpectralEnergyBound.evolve_lipschitz (f : n → ℝ) (E : ℝ) (v : EuclideanSpace ℂ n)
    (h : ∀ i, v i ≠ 0 → |f i| ≤ E) (s t : ℝ) :
    ‖evolve f t v - evolve f s v‖ ≤ E * ‖v‖ * |t - s| := by sorry
