-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroupOrbits_hermOfMom_injective
-- name    : BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:54:49.386712+00:00
-- url     : https://prove2.me/theorems/c3e95545-b560-4fa6-ae44-288008c4be2c
-- title:
--   `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective` {p q : Fin 4 → ℝ} (h : hermOfMom p = hermOfMom q) : ∀ i, p i = q i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroupOrbits`.
--
--   `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective` {p q : Fin 4 → ℝ} (h : hermOfMom p = hermOfMom q) : ∀ i, p i = q i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective`.

-- Generated from ChapterWignerLittleGroupOrbits.lean — theorem BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective
import Mathlib
import Definitions.Def_ChapterWignerLittleGroupOrbits
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroupOrbits


open Matrix Complex
open scoped ComplexOrder


open BookProof.ChapterWignerLittleGroup

theorem BookProof.ChapterWignerLittleGroupOrbits.hermOfMom_injective {p q : Fin 4 → ℝ} (h : hermOfMom p = hermOfMom q) :
    ∀ i, p i = q i := by sorry
