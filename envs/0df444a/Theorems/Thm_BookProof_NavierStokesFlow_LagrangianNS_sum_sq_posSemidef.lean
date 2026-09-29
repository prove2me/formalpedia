-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_sum_sq_posSemidef
-- name    : BookProof.NavierStokesFlow.LagrangianNS.sum_sq_posSemidef
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:28:26.135295+00:00
-- url     : https://prove2.me/theorems/fc5679a7-f787-4fab-8887-de3eed16c034
-- title:
--   The Lean 4 theorem `sum_sq_posSemidef` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum_sq_posSemidef` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.LagrangianNS.sum_sq_posSemidef
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianNS


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.LagrangianNS.sum_sq_posSemidef {m : ℕ} {R : Fin 3 → Matrix (Fin m) (Fin m) ℂ}
    (hR : ∀ i, (R i)ᴴ = R i) : (∑ i, R i * R i).PosSemidef := by sorry
