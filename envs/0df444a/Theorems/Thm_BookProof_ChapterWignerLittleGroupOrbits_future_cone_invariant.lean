-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_future_cone_invariant
-- name    : BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:55:14.990562+00:00
-- url     : https://prove2.me/theorems/be4aea55-0d18-45f4-94b8-64cd6ceeca49
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 -
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2) (h : act A (hermOfMom p) = hermOfMom q) : 0 < q 0 ∧ q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.future_cone_invariant {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (hp0 : 0 < p 0) (hmass : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2)
    (h : act A (hermOfMom p) = hermOfMom q) :
    0 < q 0 ∧ q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by sorry
