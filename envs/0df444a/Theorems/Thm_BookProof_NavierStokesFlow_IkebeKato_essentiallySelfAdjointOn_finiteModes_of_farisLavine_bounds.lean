-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
-- name    : BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T06:52:08.007261+00:00
-- url     : https://prove2.me/theorems/4e5f4f59-fd4d-40f4-aa51-50b405221c8a
-- title:
--   essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesIkebeKato.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesIkebeKato.lean

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato

variable {ι : Type*}


open scoped ENNReal



open LpNat BookProof.FarisLavine

theorem BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom c) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom c, ‖H x‖ ^ 2 ≤ a * ‖diagMax c x‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ cst * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by sorry
