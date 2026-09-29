-- Prove2me | Theorems.Thm_BookProof_FarisLavine_not_farisLavine_criterion_of_relative_bound
-- name    : BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:43:32.856985+00:00
-- url     : https://prove2.me/theorems/141a95c7-eec1-4206-ae94-677c2f2bda7f
-- title:
--   The Lean 4 theorem `not_farisLavine_criterion_of_relative_bound` in the `ChapterFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `not_farisLavine_criterion_of_relative_bound` in the `ChapterFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavine.lean

-- Generated from ChapterFarisLavine.lean — theorem BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
  BookProof.NavierStokesFlow.JacobiDeficiency in

theorem BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound :
    ¬ (∀ (D' : Submodule ℂ L2N) (H' N' : D' →ₗ[ℂ] D') (a b : ℝ),
        Dense (D' : Set L2N) →
        (∀ x y : D', (inner ℂ (H' x : L2N) (y : L2N) : ℂ) = inner ℂ (x : L2N) (H' y : L2N)) →
        (∀ v : D', ‖(H' v : L2N)‖ ≤ a * ‖(N' v : L2N)‖) →
        (∀ v : D', ‖(inner ℂ (v : L2N) ((H' (N' v) : L2N) - (N' (H' v) : L2N)) : ℂ)‖
          ≤ b * ‖(inner ℂ (v : L2N) (N' v : L2N) : ℂ)‖) →
        HasZeroDeficiencyOn D' H') := by sorry
