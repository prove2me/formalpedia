-- Prove2me | Theorems.Thm_BookProof_YangMillsBianchi_bianchi_cyclic
-- name    : BookProof.YangMillsBianchi.bianchi_cyclic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:56:38.28433+00:00
-- url     : https://prove2.me/theorems/857cbf1b-b175-4d8e-8dd2-bbcd556f1877
-- title:
--   The cyclic Jacobi identity for the double commutators of the covariant derivatives (the source of the Bianchi identity)
-- statement:
--   The cyclic Jacobi identity for the double commutators of the covariant
--   derivatives (the source of the Bianchi identity).
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsBianchi.bianchi_cyclic` (module `BookProof.YangMillsBianchi`), line-linked source: `ChapterYangMillsBianchi.lean` lines 66–70.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsBianchi.lean#L66-L70

-- Generated from ChapterYangMillsBianchi.lean — theorem BookProof.YangMillsBianchi.bianchi_cyclic
import Mathlib
import Definitions.Def_ChapterYangMillsBianchi
open BookProof.YangMillsBianchi









open BigOperators



variable {R : Type*} [Ring R]

theorem BookProof.YangMillsBianchi.bianchi_cyclic (D : Fin 3 → R) (i j k : Fin 3) :
    ⁅D i, ⁅D j, D k⁆⁆ + ⁅D j, ⁅D k, D i⁆⁆ + ⁅D k, ⁅D i, D j⁆⁆ = 0 := by sorry
