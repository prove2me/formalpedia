-- Prove2me | Theorems.Thm_BookProof_YangMillsSU3_structureConstant_antisymm_rotate
-- name    : BookProof.YangMillsSU3.structureConstant_antisymm_rotate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:08:43.54528+00:00
-- url     : https://prove2.me/theorems/9830ddf2-a286-4039-8297-4d4ca813f441
-- title:
--   The Lean 4 theorem `structureConstant_antisymm_rotate` in the `ChapterYangMillsSU3` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `structureConstant_antisymm_rotate` in the `ChapterYangMillsSU3` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsSU3.structureConstant_antisymm_rotate` (module `BookProof.YangMillsSU3`), line-linked source: `ChapterYangMillsSU3.lean` lines 90–101.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsSU3.lean#L90-L101

-- Generated from ChapterYangMillsSU3.lean — theorem BookProof.YangMillsSU3.structureConstant_antisymm_rotate
import Mathlib
import Definitions.Def_ChapterYangMillsSU3
open BookProof.YangMillsSU3







open Matrix BigOperators


variable {n d : ℕ}
variable (T : Fin d → Matrix (Fin n) (Fin n) ℂ)
variable (f : Fin d → Fin d → Fin d → ℝ)



variable {T f}

theorem BookProof.YangMillsSU3.structureConstant_antisymm_rotate
    (hT : TraceOrthonormal T) (hf : ClosesWithStructureConstants T f)
    (a b c : Fin d) :
    f a b c = - f a c b := by sorry
