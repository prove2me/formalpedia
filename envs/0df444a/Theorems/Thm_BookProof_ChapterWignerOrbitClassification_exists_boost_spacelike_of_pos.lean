-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_exists_boost_spacelike_of_pos
-- name    : BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:35.239308+00:00
-- url     : https://prove2.me/theorems/a7336d6a-81a8-4577-ab97-08e6ba5e4941
-- title:
--   `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hshell : minkSq p = -m ^ 2) (hpos : 0 < p 0 + p 3) : ∃ A : Matrix (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos` {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ) (hshell : minkSq p = -m ^ 2) (hpos : 0 < p 0 + p 3) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom (spaceRefMom m)) = hermOfMom p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos
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

theorem BookProof.ChapterWignerOrbitClassification.exists_boost_spacelike_of_pos {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hpos : 0 < p 0 + p 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by sorry
