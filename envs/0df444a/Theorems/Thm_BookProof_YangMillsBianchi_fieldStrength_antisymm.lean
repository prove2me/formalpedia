-- Prove2me | Theorems.Thm_BookProof_YangMillsBianchi_fieldStrength_antisymm
-- name    : BookProof.YangMillsBianchi.fieldStrength_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:57:16.613722+00:00
-- url     : https://prove2.me/theorems/4dd1b5aa-3ff4-4142-9376-a882ead1cd08
-- title:
--   The field strength is antisymmetric: `F_{j k} = - F_{k j}`
-- statement:
--   The field strength is antisymmetric: `F_{j k} = - F_{k j}`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsBianchi.fieldStrength_antisymm` (module `BookProof.YangMillsBianchi`), line-linked source: `ChapterYangMillsBianchi.lean` lines 60–64.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsBianchi.lean#L60-L64

-- Generated from ChapterYangMillsBianchi.lean — theorem BookProof.YangMillsBianchi.fieldStrength_antisymm
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi









open BigOperators



variable {R : Type*} [Ring R]

theorem BookProof.YangMillsBianchi.fieldStrength_antisymm (D : Fin 3 → R) (j k : Fin 3) :
    fieldStrength D j k = - fieldStrength D k j := by sorry
