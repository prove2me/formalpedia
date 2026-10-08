-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_memLpTwo_of_le
-- name    : BookProof.NavierStokesFlow.IkebeKato.memLpTwo_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:52:25.344432+00:00
-- url     : https://prove2.me/theorems/1c87d01c-0047-4e2a-8a38-fa088b0d4f26
-- title:
--   The Lean 4 theorem `memLpTwo_of_le` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.memLpTwo_of_le` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.memLpTwo_of_le
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato

variable {ι : Type*}


open scoped ENNReal



open LpNat BookProof.FarisLavine

theorem BookProof.NavierStokesFlow.IkebeKato.memLpTwo_of_le (f : L2I ι) {g : ι → ℂ} (h : ∀ k, ‖g k‖ ≤ ‖(f : ι → ℂ) k‖) :
    Memℓp g 2 := by sorry
