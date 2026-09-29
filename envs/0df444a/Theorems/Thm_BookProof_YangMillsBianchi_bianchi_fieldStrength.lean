-- Prove2me | Theorems.Thm_BookProof_YangMillsBianchi_bianchi_fieldStrength
-- name    : BookProof.YangMillsBianchi.bianchi_fieldStrength
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:08:07.650096+00:00
-- url     : https://prove2.me/theorems/a9b6b934-c7a9-4f7a-9031-95120af1a2c2
-- title:
--   The Bianchi identity written with the field strength, `ε_{i j k} [D_i, F_{j k}] = 0`
-- statement:
--   The Bianchi identity written with the field strength,
--   `ε_{i j k} [D_i, F_{j k}] = 0`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsBianchi.bianchi_fieldStrength` (module `BookProof.YangMillsBianchi`), line-linked source: `ChapterYangMillsBianchi.lean` lines 81–85.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsBianchi.lean#L81-L85

-- Generated from ChapterYangMillsBianchi.lean — theorem BookProof.YangMillsBianchi.bianchi_fieldStrength
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi









open BigOperators



variable {R : Type*} [Ring R]

theorem BookProof.YangMillsBianchi.bianchi_fieldStrength (D : Fin 3 → R) :
    ∑ i, ∑ j, ∑ k, (eps i j k) • ⁅D i, fieldStrength D j k⁆ = 0 := by sorry
