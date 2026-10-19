-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_coe_sum_single
-- name    : BookProof.NavierStokesFlow.IkebeKato.coe_sum_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T12:20:53.231075+00:00
-- url     : https://prove2.me/theorems/b2ef4b2e-7c9e-4f0c-98e9-1b3aa846ea9a
-- title:
--   The Lean 4 theorem `coe_sum_single` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coe_sum_single` in the `ChapterNavierStokesIkebeKato` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesIkebeKato.lean

-- Generated from ChapterNavierStokesIkebeKato.lean — theorem BookProof.NavierStokesFlow.IkebeKato.coe_sum_single
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.IkebeKato.coe_sum_single [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) (k : ι) :
    ((∑ i ∈ S, lp.single 2 i (u i) : L2I ι) : ι → ℂ) k = if k ∈ S then u k else 0 := by sorry
