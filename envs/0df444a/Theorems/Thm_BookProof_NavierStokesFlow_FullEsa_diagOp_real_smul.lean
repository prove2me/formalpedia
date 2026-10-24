-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagOp_real_smul
-- name    : BookProof.NavierStokesFlow.FullEsa.diagOp_real_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-23T16:54:32.659478+00:00
-- url     : https://prove2.me/theorems/3658d9a9-3088-4bf3-93fd-64a69d214cb0
-- title:
--   The Lean 4 theorem `diagOp_real_smul` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagOp_real_smul` in the `ChapterNavierStokesFullEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullEsa.lean

-- Generated from ChapterNavierStokesFullEsa.lean — theorem BookProof.NavierStokesFlow.FullEsa.diagOp_real_smul
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

theorem BookProof.NavierStokesFlow.FullEsa.diagOp_real_smul (r : ℝ) (a : ℕ → ℝ) :
    ((r : ℂ)) • diagOp a = diagOp (fun n => r * a n) := by sorry
