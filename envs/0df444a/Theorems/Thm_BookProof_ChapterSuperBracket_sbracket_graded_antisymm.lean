-- Prove2me | Theorems.Thm_BookProof_ChapterSuperBracket_sbracket_graded_antisymm
-- name    : BookProof.ChapterSuperBracket.sbracket_graded_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:42.510687+00:00
-- url     : https://prove2.me/theorems/406bf319-a932-4f53-8f56-1a9d018b2855
-- title:
--   `BookProof.ChapterSuperBracket.sbracket_graded_antisymm` (p q : Bool) (a b : R) : sbracket p q a b = - (eps p q : R) * sbracket q p b a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSuperBracket`.
--
--   `BookProof.ChapterSuperBracket.sbracket_graded_antisymm` (p q : Bool) (a b : R) : sbracket p q a b = - (eps p q : R) * sbracket q p b a
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSuperBracket.sbracket_graded_antisymm`.

-- Generated from ChapterSuperBracket.lean — theorem BookProof.ChapterSuperBracket.sbracket_graded_antisymm
import Mathlib
import Definitions.Def_ChapterSuperBracket
import Definitions.Def_ChapterElectroweakFieldStrength
open BookProof.ChapterElectroweakFieldStrength
open BookProof.ChapterSuperBracket



variable {R : Type*} [Ring R]

theorem BookProof.ChapterSuperBracket.sbracket_graded_antisymm (p q : Bool) (a b : R) :
    sbracket p q a b = - (eps p q : R) * sbracket q p b a := by sorry
