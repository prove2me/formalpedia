-- Prove2me | Theorems.Thm_BookProof_ChapterParity_higgsParity_order_four
-- name    : BookProof.ChapterParity.higgsParity_order_four
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T09:05:00.674583+00:00
-- url     : https://prove2.me/theorems/535e0880-385f-48b7-9c4e-b28895a72ad1
-- title:
--   `BookProof.ChapterParity.higgsParity_order_four` : higgsParity * higgsParity ≠ 1 ∧ higgsParity * higgsParity * (higgsParity * higgsParity) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.higgsParity_order_four` : higgsParity * higgsParity ≠ 1 ∧ higgsParity * higgsParity * (higgsParity * higgsParity) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.higgsParity_order_four`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.higgsParity_order_four
import Mathlib
import Definitions.Def_ChapterParity
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.higgsParity_order_four :
    higgsParity * higgsParity ≠ 1 ∧
      higgsParity * higgsParity * (higgsParity * higgsParity) = 1 := by sorry
