-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_coe_sum_apply_prime
-- name    : BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:29.346775+00:00
-- url     : https://prove2.me/theorems/09c22fa0-fd9d-41cb-a26a-ded53bf262ea
-- title:
--   BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply'
-- statement:
--   BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply'

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply'
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.coe_sum_apply_prime (s : Finset (Fin d)) (v : Fin d → L2I (Occ d)) (α : Occ d) :
    (((∑ i ∈ s, v i : L2I (Occ d))) : Occ d → ℂ) α
      = ∑ i ∈ s, ((v i : L2I (Occ d)) : Occ d → ℂ) α := by sorry
