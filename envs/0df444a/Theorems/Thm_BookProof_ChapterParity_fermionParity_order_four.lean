-- Prove2me | Theorems.Thm_BookProof_ChapterParity_fermionParity_order_four
-- name    : BookProof.ChapterParity.fermionParity_order_four
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T00:07:07.624997+00:00
-- url     : https://prove2.me/theorems/2d71cf45-b1a2-4ded-b878-570a507d11bf
-- title:
--   `BookProof.ChapterParity.fermionParity_order_four` : mgamma 0 * mgamma 0 ≠ 1 ∧ mgamma 0 * mgamma 0 * (mgamma 0 * mgamma 0) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParity`.
--
--   `BookProof.ChapterParity.fermionParity_order_four` : mgamma 0 * mgamma 0 ≠ 1 ∧ mgamma 0 * mgamma 0 * (mgamma 0 * mgamma 0) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParity.fermionParity_order_four`.

-- Generated from ChapterParity.lean — theorem BookProof.ChapterParity.fermionParity_order_four
import Mathlib
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterA3
open BookProof.ChapterA3
open BookProof.ChapterParity


open Matrix
open scoped ComplexConjugate

variable {n : Type*}

theorem BookProof.ChapterParity.fermionParity_order_four :
    mgamma 0 * mgamma 0 ≠ 1 ∧
      mgamma 0 * mgamma 0 * (mgamma 0 * mgamma 0) = 1 := by sorry
