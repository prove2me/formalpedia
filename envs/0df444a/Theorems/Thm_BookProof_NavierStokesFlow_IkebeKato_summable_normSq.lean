-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_summable_normSq
-- name    : BookProof.NavierStokesFlow.IkebeKato.summable_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-04T13:52:58.739984+00:00
-- url     : https://prove2.me/theorems/197e5584-4cfb-4dea-a184-c96e698e8e8a
-- title:
--   The Lean 4 theorem `summable_normSq` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.summable_normSq` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.summable_normSq
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato

variable {ι : Type*}


open scoped ENNReal



open LpNat BookProof.FarisLavine

theorem BookProof.NavierStokesFlow.IkebeKato.summable_normSq (f : L2I ι) : Summable fun k => ‖(f : ι → ℂ) k‖ ^ 2 := by sorry
