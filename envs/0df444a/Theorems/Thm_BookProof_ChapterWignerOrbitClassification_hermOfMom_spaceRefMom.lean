-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_hermOfMom_spaceRefMom
-- name    : BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:14:39.65599+00:00
-- url     : https://prove2.me/theorems/82be4c4e-d35a-4429-9a3c-b056278ad372
-- title:
--   `BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom` (m : ℝ) : hermOfMom (spaceRefMom m) = !![(m : ℂ), 0; 0, -(m : ℂ)]
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom` (m : ℝ) : hermOfMom (spaceRefMom m) = !![(m : ℂ), 0; 0, -(m : ℂ)]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.hermOfMom_spaceRefMom (m : ℝ) :
    hermOfMom (spaceRefMom m) = !![(m : ℂ), 0; 0, -(m : ℂ)] := by sorry
