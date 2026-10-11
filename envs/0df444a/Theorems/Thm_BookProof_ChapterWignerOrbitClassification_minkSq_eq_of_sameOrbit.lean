-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_minkSq_eq_of_sameOrbit
-- name    : BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:14:38.321018+00:00
-- url     : https://prove2.me/theorems/eec8b2ba-1bed-4d2c-b8d4-fae6ca039917
-- title:
--   `BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit` {p q : Fin 4 → ℝ} (h : SameOrbit p q) : minkSq p = minkSq q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit` {p q : Fin 4 → ℝ} (h : SameOrbit p q) : minkSq p = minkSq q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit
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

theorem BookProof.ChapterWignerOrbitClassification.minkSq_eq_of_sameOrbit {p q : Fin 4 → ℝ} (h : SameOrbit p q) : minkSq p = minkSq q := by sorry
