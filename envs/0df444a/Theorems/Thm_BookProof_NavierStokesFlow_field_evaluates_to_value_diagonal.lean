-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_field_evaluates_to_value_diagonal
-- name    : BookProof.NavierStokesFlow.field_evaluates_to_value_diagonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:28:33.244132+00:00
-- url     : https://prove2.me/theorems/95fb81dd-69ae-4165-81f8-5640d0ff79f4
-- title:
--   The Lean 4 theorem `field_evaluates_to_value_diagonal` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `field_evaluates_to_value_diagonal` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.field_evaluates_to_value_diagonal
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.field_evaluates_to_value_diagonal {m : ℕ} (xs : Fin 3 → Fin m → ℂ) (k : Fin m)
    (phi : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (phiD : Fin 3 → (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) :
    fieldTaylor phi phiD (fun i => Matrix.mulVecLin (Matrix.diagonal (xs i)))
        (fun i => xs i k) (Pi.single k 1)
      = phi (Pi.single k 1) := by sorry
