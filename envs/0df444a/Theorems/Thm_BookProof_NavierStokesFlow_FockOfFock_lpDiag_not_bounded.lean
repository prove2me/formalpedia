-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_not_bounded
-- name    : BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:34.53666+00:00
-- url     : https://prove2.me/theorems/c571400f-31f1-4da1-a28d-b74f3f4d478a
-- title:
--   (c : ι → ℝ) (hc : ∀ C : ℝ, ∃ i, C < |c i|) : ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ι, ‖lpDiag c f‖ ≤ C * ‖f‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockSpace.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock








open FullEsa



variable {ι : Type*}














variable {ι : Type*}

theorem BookProof.NavierStokesFlow.FockOfFock.lpDiag_not_bounded (c : ι → ℝ) (hc : ∀ C : ℝ, ∃ i, C < |c i|) :
    ¬ ∃ C : ℝ, ∀ f : lpFiniteModes ι, ‖lpDiag c f‖ ≤ C * ‖f‖ := by sorry
