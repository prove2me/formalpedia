-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_fock_comparison_eq
-- name    : BookProof.NavierStokesFlow.FockCanonical.fock_comparison_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:16:18.542415+00:00
-- url     : https://prove2.me/theorems/f5d9c2d0-a4d1-4a1f-96f9-bf82a121256b
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) : (lpFiniteModes (Occ d)).subtype.comp ((∑ i, ((mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i))) + LinearMap.id) = (diagMax (fockSym κ)).comp...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.fock_comparison_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.fock_comparison_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.Bosonic
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.fock_comparison_eq (hκ : ∀ i, 0 ≤ κ i) :
    (lpFiniteModes (Occ d)).subtype.comp
        ((∑ i, ((mom κ i).comp (mom κ i) + (drift κ i).comp (drift κ i))) + LinearMap.id)
      = (diagMax (fockSym κ)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by sorry
