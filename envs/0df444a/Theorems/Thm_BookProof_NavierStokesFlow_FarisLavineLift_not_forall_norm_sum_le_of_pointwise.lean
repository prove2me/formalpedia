-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_not_forall_norm_sum_le_of_pointwise
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:21:02.227973+00:00
-- url     : https://prove2.me/theorems/267bcd32-8cc2-4303-b0b2-d3b2df0f2615
-- title:
--   : ∃ (h n : Fin 2 → (E2 →ₗ[ℂ] E2)) (v : E2), (∀ (k : Fin 2) (x : E2), ‖h k x‖ ≤ ‖n k x‖) ∧ ‖(n 0 + n 1) v‖ < ‖(h 0 + h 1) v‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise :
    ∃ (h n : Fin 2 → (E2 →ₗ[ℂ] E2)) (v : E2),
      (∀ (k : Fin 2) (x : E2), ‖h k x‖ ≤ ‖n k x‖) ∧
        ‖(n 0 + n 1) v‖ < ‖(h 0 + h 1) v‖ := by sorry
