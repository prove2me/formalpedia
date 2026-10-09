-- Prove2me | Theorems.Thm_BookProof_FreeEMField_fieldStrengthMul_eq_emFieldStrength_of_commute
-- name    : BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:24:49.19103+00:00
-- url     : https://prove2.me/theorems/98356df2-239a-4e71-805f-a5ccdc1d533b
-- title:
--   `BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute` (δ : Fin 3 → R → R) (a : Fin 3 → R) (hcommute : ∀ j k, a j * a k = a k * a j) (j k : Fin 3) : fieldStrengthMu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeEMField`.
--
--   `BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute` (δ : Fin 3 → R → R) (a : Fin 3 → R) (hcommute : ∀ j k, a j * a k = a k * a j) (j k : Fin 3) : fieldStrengthMul δ a j k = emFieldStrength δ a j k
--
--   Formalization note: Lean 4 identifier `BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute`.

-- Generated from ChapterFreeEMField.lean — theorem BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute
import Mathlib
import Definitions.Def_ChapterFreeEMField
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength
open BookProof.FreeEMField



open BookProof.YangMillsFieldStrength


variable {R : Type*} [Ring R]

theorem BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute
    (δ : Fin 3 → R → R) (a : Fin 3 → R)
    (hcommute : ∀ j k, a j * a k = a k * a j) (j k : Fin 3) :
    fieldStrengthMul δ a j k = emFieldStrength δ a j k := by sorry
