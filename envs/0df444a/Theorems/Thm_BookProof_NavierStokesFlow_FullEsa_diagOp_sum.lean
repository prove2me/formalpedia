-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagOp_sum
-- name    : BookProof.NavierStokesFlow.FullEsa.diagOp_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-23T16:54:33.617734+00:00
-- url     : https://prove2.me/theorems/edef284e-3cbc-459f-8b49-ba4dd1d0730d
-- title:
--   The Lean 4 theorem `diagOp_sum` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagOp_sum` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullEsa.lean

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagOp_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.DiagonalEsa


open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

theorem BookProof.NavierStokesFlow.FullEsa.diagOp_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ) :
    (∑ i ∈ s, diagOp (a i)) = diagOp (fun n => ∑ i ∈ s, a i n) := by sorry
