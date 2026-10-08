-- Prove2me | Theorems.Thm_BookProof_FreeEMField_emFieldStrength_antisymm
-- name    : BookProof.FreeEMField.emFieldStrength_antisymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:25:21.422839+00:00
-- url     : https://prove2.me/theorems/1af88392-e42a-415a-aefd-15d7189a97b0
-- title:
--   `BookProof.FreeEMField.emFieldStrength_antisymm` (δ : Fin 3 → R → R) (A : Fin 3 → R) (j k : Fin 3) : emFieldStrength δ A j k = - emFieldStrength δ A k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeEMField`.
--
--   `BookProof.FreeEMField.emFieldStrength_antisymm` (δ : Fin 3 → R → R) (A : Fin 3 → R) (j k : Fin 3) : emFieldStrength δ A j k = - emFieldStrength δ A k j
--
--   Formalization note: Lean 4 identifier `BookProof.FreeEMField.emFieldStrength_antisymm`.

-- Generated from ChapterFreeEMField.lean — theorem BookProof.FreeEMField.emFieldStrength_antisymm
import Definitions.Def_ChapterYangMillsFieldStrength
import Mathlib
import Definitions.Def_ChapterFreeEMField
open BookProof.FreeEMField



open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

theorem BookProof.FreeEMField.emFieldStrength_antisymm (δ : Fin 3 → R → R) (A : Fin 3 → R) (j k : Fin 3) :
    emFieldStrength δ A j k = - emFieldStrength δ A k j := by sorry
