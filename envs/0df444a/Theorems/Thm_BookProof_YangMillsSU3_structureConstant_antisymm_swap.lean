-- Prove2me | Theorems.Thm_BookProof_YangMillsSU3_structureConstant_antisymm_swap
-- name    : BookProof.YangMillsSU3.structureConstant_antisymm_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:09:18.786244+00:00
-- url     : https://prove2.me/theorems/b38a983c-7e44-4642-bfc9-4de6775e475f
-- title:
--   The Lean 4 theorem `structureConstant_antisymm_swap` in the `ChapterYangMillsSU3` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `structureConstant_antisymm_swap` in the `ChapterYangMillsSU3` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsSU3.structureConstant_antisymm_swap` (module `BookProof.YangMillsSU3`), line-linked source: `ChapterYangMillsSU3.lean` lines 77–84.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsSU3.lean#L77-L84

-- Generated from ChapterYangMillsSU3.lean — theorem BookProof.YangMillsSU3.structureConstant_antisymm_swap
import Mathlib
import Definitions.Def_ChapterYangMillsSU3
open BookProof.YangMillsSU3







open Matrix BigOperators


variable {n d : ℕ}
variable (T : Fin d → Matrix (Fin n) (Fin n) ℂ)
variable (f : Fin d → Fin d → Fin d → ℝ)



variable {T f}

theorem BookProof.YangMillsSU3.structureConstant_antisymm_swap
    (hT : TraceOrthonormal T) (hf : ClosesWithStructureConstants T f)
    (a b c : Fin d) :
    f a b c = - f b a c := by sorry
