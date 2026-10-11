-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_sameOrbit_negMom
-- name    : BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:16:44.393815+00:00
-- url     : https://prove2.me/theorems/cd3df0b9-26f7-4037-b729-8197847172c0
-- title:
--   `BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom` {p q : Fin 4 → ℝ} (h : SameOrbit p q) : SameOrbit (negMom p) (negMom q)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom` {p q : Fin 4 → ℝ} (h : SameOrbit p q) : SameOrbit (negMom p) (negMom q)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.sameOrbit_negMom {p q : Fin 4 → ℝ} (h : SameOrbit p q) :
    SameOrbit (negMom p) (negMom q) := by sorry
