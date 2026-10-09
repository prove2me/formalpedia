-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
-- name    : BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:21:36.998354+00:00
-- url     : https://prove2.me/theorems/ff325936-99a2-45b4-b175-842cf2b78080
-- title:
--   The Lean 4 theorem `diagMax_quadForm_nonneg` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_nonneg (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (x : maxDom c) :
    0 ≤ quadForm (diagMax c) x := by sorry
