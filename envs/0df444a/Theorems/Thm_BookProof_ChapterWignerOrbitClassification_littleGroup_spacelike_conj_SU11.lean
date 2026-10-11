-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_littleGroup_spacelike_conj_SU11
-- name    : BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:15:41.834362+00:00
-- url     : https://prove2.me/theorems/f9811ff8-3e17-435f-b5c3-48bc75ef7ec3
-- title:
--   `BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11` {p : Fin 4 → ℝ} (hneg : minkSq p < 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ littleGroup p = (fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11` {p : Fin 4 → ℝ} (hneg : minkSq p < 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ littleGroup p = (fun B => A * B * A⁻¹) '' SU11
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterLittleGroup
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
open BookProof.ChapterGravityProjector
open BookProof.ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.littleGroup_spacelike_conj_SU11 {p : Fin 4 → ℝ} (hneg : minkSq p < 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SU11 := by sorry
