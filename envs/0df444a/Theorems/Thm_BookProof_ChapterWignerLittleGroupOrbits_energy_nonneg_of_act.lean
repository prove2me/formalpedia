-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_energy_nonneg_of_act
-- name    : BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:54:46.944578+00:00
-- url     : https://prove2.me/theorems/a339d97c-b562-4edf-a047-64c02ae38e03
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act` {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 4 → ℝ} (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act` {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 4 → ℝ} (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) (h : act A (hermOfMom p) = hermOfMom q) : 0 ≤ q 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.energy_nonneg_of_act {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : Fin 4 → ℝ}
    (hp0 : 0 ≤ p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) : 0 ≤ q 0 := by sorry
