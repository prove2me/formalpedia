-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_posSemidef
-- name    : BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:54:54.97607+00:00
-- url     : https://prove2.me/theorems/97b70fee-6cfe-4d3f-96b6-679da97e58a1
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef` {p : Fin 4 → ℝ} (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) : (hermOfMom p).PosSemidef
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef` {p : Fin 4 → ℝ} (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) : (hermOfMom p).PosSemidef
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_posSemidef {p : Fin 4 → ℝ} (hp0 : 0 ≤ p 0)
    (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) :
    (hermOfMom p).PosSemidef := by sorry
