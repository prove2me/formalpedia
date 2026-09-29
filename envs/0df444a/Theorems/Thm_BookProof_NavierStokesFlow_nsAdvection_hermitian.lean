-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsAdvection_hermitian
-- name    : BookProof.NavierStokesFlow.nsAdvection_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:52:44.08042+00:00
-- url     : https://prove2.me/theorems/e744df99-0bb7-4a24-9d97-ba1b05533c1b
-- title:
--   The Lean 4 theorem `nsAdvection_hermitian` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsAdvection_hermitian` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsAdvection_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsAdvection_hermitian (i : Fin 3) : (nsAdvection d i)ᴴ = nsAdvection d i := by sorry
