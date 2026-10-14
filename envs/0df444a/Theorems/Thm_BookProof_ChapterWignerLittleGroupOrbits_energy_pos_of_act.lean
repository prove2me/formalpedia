-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_energy_pos_of_act
-- name    : BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:55:30.981321+00:00
-- url     : https://prove2.me/theorems/c0b1ecaa-e9c2-4912-a356-a782c993bfa6
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) (h : act A (hermOfMom p) = hermOfMom q) : 0 < q 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.energy_pos_of_act {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) : 0 < q 0 := by sorry
