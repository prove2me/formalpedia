-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_coe_sum_apply
-- name    : BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:12:34.475753+00:00
-- url     : https://prove2.me/theorems/c2138956-7d0d-4c4c-8b11-056c7d2d7c1b
-- title:
--   (s : Finset (Fin d)) (v : Fin d → lpFiniteModes (Occ d)) (α : Occ d) : (((∑ i ∈ s, v i : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α = ∑ i ∈ s, (((v i : lpFiniteModes...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply (s : Finset (Fin d)) (v : Fin d → lpFiniteModes (Occ d)) (α : Occ d) :
    (((∑ i ∈ s, v i : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α
      = ∑ i ∈ s, (((v i : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) α := by sorry
