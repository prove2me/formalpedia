-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hermitian
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:54:07.855088+00:00
-- url     : https://prove2.me/theorems/092061f5-fe8a-4907-824c-2cb2a4c4d527
-- title:
--   The Lean 4 theorem `nsHamiltonian_hermitian` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_hermitian` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsHamiltonian_hermitian : (nsHamiltonian d)ᴴ = nsHamiltonian d := by sorry
