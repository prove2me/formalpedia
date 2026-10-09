-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_sum_single_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T05:00:08.960509+00:00
-- url     : https://prove2.me/theorems/7fb3899e-0865-43d3-a268-8851da31a63b
-- title:
--   The Lean 4 theorem `sum_single_mem_finiteModes` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) :
    (∑ i ∈ S, lp.single 2 i (u i) : L2I ι) ∈ lpFiniteModes ι := by sorry
