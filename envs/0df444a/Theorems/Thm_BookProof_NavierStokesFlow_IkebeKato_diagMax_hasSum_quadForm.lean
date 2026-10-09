-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_hasSum_quadForm
-- name    : BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:22:36.644038+00:00
-- url     : https://prove2.me/theorems/50d0b0b6-6563-4171-857d-5b2847f6e4f5
-- title:
--   The Lean 4 theorem `diagMax_hasSum_quadForm` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm (c : ι → ℝ) (x : maxDom c) :
    HasSum (fun k => c k * ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2) (quadForm (diagMax c) x) := by sorry
