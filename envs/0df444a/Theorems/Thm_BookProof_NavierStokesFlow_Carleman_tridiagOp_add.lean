-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_add
-- name    : BookProof.NavierStokesFlow.Carleman.tridiagOp_add
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:36:50.032983+00:00
-- url     : https://prove2.me/theorems/d8c4752e-c73a-4eb2-b04a-4b6c67ecb9f4
-- title:
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_add` (c c' : ℕ → ℂ) : tridiagOp c + tridiagOp c' = tridiagOp (fun n => c n + c' n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.tridiagOp_add` (c c' : ℕ → ℂ) : tridiagOp c + tridiagOp c' = tridiagOp (fun n => c n + c' n)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.tridiagOp_add`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_add
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.tridiagOp_add (c c' : ℕ → ℂ) :
    tridiagOp c + tridiagOp c' = tridiagOp (fun n => c n + c' n) := by sorry
