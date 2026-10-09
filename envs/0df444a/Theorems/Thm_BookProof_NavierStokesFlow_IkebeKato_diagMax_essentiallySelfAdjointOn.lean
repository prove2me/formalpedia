-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_essentiallySelfAdjointOn
-- name    : BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:22:31.786059+00:00
-- url     : https://prove2.me/theorems/e87ad437-8f00-4457-864b-d99ee76e6f66
-- title:
--   The Lean 4 theorem `diagMax_essentiallySelfAdjointOn` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (maxDom c) (diagMax c) := by sorry
