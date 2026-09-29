-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsBrst_nilpotent
-- name    : BookProof.NavierStokesFlow.nsBrst_nilpotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:27.196561+00:00
-- url     : https://prove2.me/theorems/d0fd636c-20a5-49c8-b5b2-02ca983bb377
-- title:
--   The Lean 4 theorem `nsBrst_nilpotent` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsBrst_nilpotent` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsBrst_nilpotent
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsBrst_nilpotent : nsBrstCharge d * nsBrstCharge d = 0 := by sorry
