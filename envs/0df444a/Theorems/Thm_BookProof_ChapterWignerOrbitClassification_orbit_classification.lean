-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_orbit_classification
-- name    : BookProof.ChapterWignerOrbitClassification.orbit_classification
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:16:52.426055+00:00
-- url     : https://prove2.me/theorems/ccd54c2a-59ac-45f9-8a26-72ee67fca177
-- title:
--   `BookProof.ChapterWignerOrbitClassification.orbit_classification` (p q : Fin 4 → ℝ) : SameOrbit p q ↔ minkSq p = minkSq q ∧ (minkSq p < 0 ∨ ((∀ i, p i = 0) ∧ (∀ i, q i = 0)) ∨ (0 <
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.orbit_classification` (p q : Fin 4 → ℝ) : SameOrbit p q ↔ minkSq p = minkSq q ∧ (minkSq p < 0 ∨ ((∀ i, p i = 0) ∧ (∀ i, q i = 0)) ∨ (0 < p 0 ∧ 0 < q 0) ∨ (p 0 < 0 ∧ q 0 < 0))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.orbit_classification`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.orbit_classification
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

theorem BookProof.ChapterWignerOrbitClassification.orbit_classification (p q : Fin 4 → ℝ) :
    SameOrbit p q ↔ minkSq p = minkSq q ∧
      (minkSq p < 0 ∨ ((∀ i, p i = 0) ∧ (∀ i, q i = 0)) ∨ (0 < p 0 ∧ 0 < q 0) ∨
        (p 0 < 0 ∧ q 0 < 0)) := by sorry
