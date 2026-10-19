-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFullData_advection
-- name    : BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:56:54.339471+00:00
-- url     : https://prove2.me/theorems/a200f8a2-b95a-4e92-8ff0-05dbefce1954
-- title:
--   `BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) : (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection` (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) : (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.halfLineFullData_advection (c : Fin 15 → ℕ → ℝ) (nu : ℝ) (i : Fin 3) :
    (halfLineFullData c nu).advection i = diagOp (halfLineAlpha c nu i) := by sorry
