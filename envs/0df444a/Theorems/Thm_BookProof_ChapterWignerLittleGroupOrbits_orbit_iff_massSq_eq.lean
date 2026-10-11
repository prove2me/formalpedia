-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_orbit_iff_massSq_eq
-- name    : BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:55:39.878648+00:00
-- url     : https://prove2.me/theorems/3132e41f-6243-43e8-907b-911f36a58b03
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq` {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hq0 : 0 < q 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) : (∃ A : Matrix
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq` {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hq0 : 0 < q 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) : (∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom p) = hermOfMom q) ↔ q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.orbit_iff_massSq_eq {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hq0 : 0 < q 0)
    (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) :
    (∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom p) = hermOfMom q) ↔
      q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by sorry
