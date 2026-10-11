-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike_of_zero
-- name    : BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:15:33.330667+00:00
-- url     : https://prove2.me/theorems/c3fab72e-40fd-479e-ac31-b36f9bf5efbe
-- title:
--   `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hshell : minkSq p = -m ^ 2) (hzero : p 0 + p 3 = 0) : ∃ A : Matrix
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hshell : minkSq p = -m ^ 2) (hzero : p 0 + p 3 = 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom (spaceRefMom m)) = hermOfMom p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterGravityProjector
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_zero {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hzero : p 0 + p 3 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by sorry
