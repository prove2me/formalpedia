-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_negMom_negMom
-- name    : BookProof.ChapterWignerOrbitClassification.negMom_negMom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:08.630978+00:00
-- url     : https://prove2.me/theorems/7e6e35bb-51df-4b3d-99b8-60e8e3aac121
-- title:
--   `BookProof.ChapterWignerOrbitClassification.negMom_negMom` (p : Fin 4 → ℝ) : negMom (negMom p) = p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.negMom_negMom` (p : Fin 4 → ℝ) : negMom (negMom p) = p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.negMom_negMom`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.negMom_negMom
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.negMom_negMom (p : Fin 4 → ℝ) : negMom (negMom p) = p := by sorry
