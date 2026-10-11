-- Prove2me | Theorems.Thm_BookProof_ChapterWignerOrbitClassification_eq_zero_of_energy_zero
-- name    : BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:17:57.250184+00:00
-- url     : https://prove2.me/theorems/8c8eca65-0b31-4e12-942a-9a303bf57e7c
-- title:
--   `BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero` {p : Fin 4 → ℝ} (hmass : 0 ≤ minkSq p) (h0 : p 0 = 0) : ∀ i, p i = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerOrbitClassification`.
--
--   `BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero` {p : Fin 4 → ℝ} (hmass : 0 ≤ minkSq p) (h0 : p 0 = 0) : ∀ i, p i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero`.

-- Generated from ChapterWignerOrbitClassification.lean — theorem BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Mathlib
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector
open BookProof.ChapterWignerOrbitClassification


open Matrix Complex


open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

theorem BookProof.ChapterWignerOrbitClassification.eq_zero_of_energy_zero {p : Fin 4 → ℝ} (hmass : 0 ≤ minkSq p) (h0 : p 0 = 0) :
    ∀ i, p i = 0 := by sorry
