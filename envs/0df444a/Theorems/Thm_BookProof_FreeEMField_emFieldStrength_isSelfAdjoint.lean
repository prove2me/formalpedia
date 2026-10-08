-- Prove2me | Theorems.Thm_BookProof_FreeEMField_emFieldStrength_isSelfAdjoint
-- name    : BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:28:01.212558+00:00
-- url     : https://prove2.me/theorems/f6aae672-a8eb-4e21-9049-2c88ec0a9e12
-- title:
--   `BookProof.FreeEMField.emFieldStrength_isSelfAdjoint` (δ : Fin 3 → R → R) (π : Fin 3 → R) (hstar : ∀ (j : Fin 3) x, star (δ j x) = δ j (star x)) (hsa : ∀ i, IsSelfAdjoint (π i)) (j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeEMField`.
--
--   `BookProof.FreeEMField.emFieldStrength_isSelfAdjoint` (δ : Fin 3 → R → R) (π : Fin 3 → R) (hstar : ∀ (j : Fin 3) x, star (δ j x) = δ j (star x)) (hsa : ∀ i, IsSelfAdjoint (π i)) (j k : Fin 3) : IsSelfAdjoint (emFieldStrength δ π j k)
--
--   Formalization note: Lean 4 identifier `BookProof.FreeEMField.emFieldStrength_isSelfAdjoint`.

-- Generated from ChapterFreeEMField.lean — theorem BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
import Definitions.Def_ChapterYangMillsFieldStrength
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField



open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {R : Type*} [Ring R] [StarRing R]

theorem BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
    (δ : Fin 3 → R → R) (π : Fin 3 → R)
    (hstar : ∀ (j : Fin 3) x, star (δ j x) = δ j (star x))
    (hsa : ∀ i, IsSelfAdjoint (π i)) (j k : Fin 3) :
    IsSelfAdjoint (emFieldStrength δ π j k) := by sorry
