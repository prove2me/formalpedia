-- Prove2me | Theorems.Thm_BookProof_YangMillsSU3_structureConstant_totally_antisymmetric
-- name    : BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:11:49.958212+00:00
-- url     : https://prove2.me/theorems/c0082dd5-63b2-4da9-bc4b-25465d8db921
-- title:
--   Total antisymmetry** of the structure constants: swapping the first two or the last two indices flips the sign
-- statement:
--   **Total antisymmetry** of the structure constants: swapping the first two
--   or the last two indices flips the sign.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsSU3.structureConstant_totally_antisymmetric` (module `BookProof.YangMillsSU3`), line-linked source: `ChapterYangMillsSU3.lean` lines 103–108.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsSU3.lean#L103-L108

-- Generated from ChapterYangMillsSU3.lean — theorem BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
import Mathlib
import Definitions.Def_ChapterYangMillsSU3
open BookProof.YangMillsSU3







open Matrix BigOperators


variable {n d : ℕ}
variable (T : Fin d → Matrix (Fin n) (Fin n) ℂ)
variable (f : Fin d → Fin d → Fin d → ℝ)



variable {T f}

theorem BookProof.YangMillsSU3.structureConstant_totally_antisymmetric
    (hT : TraceOrthonormal T) (hf : ClosesWithStructureConstants T f) :
    (∀ a b c, f a b c = - f b a c) ∧ (∀ a b c, f a b c = - f a c b) := by sorry
