-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_mass_invariant
-- name    : BookProof.ChapterWignerLittleGroup.mass_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:52:42.356979+00:00
-- url     : https://prove2.me/theorems/155b91f1-87df-4532-b0b5-2ee98f78c0b6
-- title:
--   `BookProof.ChapterWignerLittleGroup.mass_invariant` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (h : act A (hermOfMom p) = hermOfMom q) : q 0 ^ 2 - q 1 ^ 2 -
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.mass_invariant` {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ} (h : act A (hermOfMom p) = hermOfMom q) : q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.mass_invariant`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.mass_invariant
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.mass_invariant {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {p q : Fin 4 → ℝ}
    (h : act A (hermOfMom p) = hermOfMom q) :
    q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by sorry
