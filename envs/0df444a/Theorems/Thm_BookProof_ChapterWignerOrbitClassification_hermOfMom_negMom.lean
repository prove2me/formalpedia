-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_hermOfMom_negMom
-- name    : BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:04.030322+00:00
-- url     : https://prove2.me/theorems/ca21d723-7fc7-4cce-8610-b136ad5b644c
-- title:
--   `BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom` (p : Fin 4 → ℝ) : hermOfMom (negMom p) = -hermOfMom p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom` (p : Fin 4 → ℝ) : hermOfMom (negMom p) = -hermOfMom p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.hermOfMom_negMom (p : Fin 4 → ℝ) : hermOfMom (negMom p) = -hermOfMom p := by sorry
