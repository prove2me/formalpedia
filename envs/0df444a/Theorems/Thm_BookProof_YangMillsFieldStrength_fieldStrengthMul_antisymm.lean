-- Prove2me | Theorems.Thm_BookProof_YangMillsFieldStrength_fieldStrengthMul_antisymm
-- name    : BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:52:44.814741+00:00
-- url     : https://prove2.me/theorems/c8c487a8-95eb-4145-a877-60b9a332f088
-- title:
--   The field strength is antisymmetric: `F_{j k} = - F_{k j}`
-- statement:
--   The field strength is antisymmetric: `F_{j k} = - F_{k j}`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm` (module `BookProof.YangMillsFieldStrength`), line-linked source: `ChapterYangMillsFieldStrength.lean` lines 107–110.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFieldStrength.lean#L107-L110

-- Generated from ChapterYangMillsFieldStrength.lean — theorem BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm
import Mathlib
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength













open Complex



variable {R : Type*} [Ring R]

theorem BookProof.YangMillsFieldStrength.fieldStrengthMul_antisymm (δ : Fin 3 → R → R) (a : Fin 3 → R) (j k : Fin 3) :
    fieldStrengthMul δ a j k = - fieldStrengthMul δ a k j := by sorry
