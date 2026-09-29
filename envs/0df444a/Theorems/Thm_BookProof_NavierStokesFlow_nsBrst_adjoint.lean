-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsBrst_adjoint
-- name    : BookProof.NavierStokesFlow.nsBrst_adjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:15.189035+00:00
-- url     : https://prove2.me/theorems/d9c1b16a-7eed-4f29-abd0-c021a92be182
-- title:
--   The Lean 4 theorem `nsBrst_adjoint` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsBrst_adjoint` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsBrst_adjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsBrst_adjoint : (nsBrstCharge d)ᴴ = nsDivergence d ⊗ₖ BookProof.GhostField.psi := by sorry
