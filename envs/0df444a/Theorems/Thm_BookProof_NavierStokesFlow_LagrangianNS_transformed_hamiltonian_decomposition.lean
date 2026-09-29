-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_transformed_hamiltonian_decomposition
-- name    : BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:52:33.011672+00:00
-- url     : https://prove2.me/theorems/a919533c-cfa9-42f6-95b2-bf8e0cd71ece
-- title:
--   The Lean 4 theorem `transformed_hamiltonian_decomposition` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `transformed_hamiltonian_decomposition` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianNS


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (L : LagrangianNS n)

theorem BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition :
    L.hFull = L.kinetic + L.viscous + L.drift + L.C := by sorry
