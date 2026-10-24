-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagOp_sub
-- name    : BookProof.NavierStokesFlow.FullEsa.diagOp_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-23T16:54:32.992468+00:00
-- url     : https://prove2.me/theorems/87211c94-a624-49df-89a7-6533d175a0df
-- title:
--   The Lean 4 theorem `diagOp_sub` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagOp_sub` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullEsa.lean

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagOp_sub
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

theorem BookProof.NavierStokesFlow.FullEsa.diagOp_sub (a b : ℕ → ℝ) : diagOp a - diagOp b = diagOp (fun n => a n - b n) := by sorry
