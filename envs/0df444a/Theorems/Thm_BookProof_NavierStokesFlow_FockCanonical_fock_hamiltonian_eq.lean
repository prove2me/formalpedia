-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_fock_hamiltonian_eq
-- name    : BookProof.NavierStokesFlow.FockCanonical.fock_hamiltonian_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T16:03:26.467059+00:00
-- url     : https://prove2.me/theorems/61074160-51eb-4f52-8d1d-9e764250027f
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) : (lpFiniteModes (Occ d)).subtype.comp (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i))) = (fockH hκ).comp (Submodule.inclusion...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.fock_hamiltonian_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.fock_hamiltonian_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.fock_hamiltonian_eq (hκ : ∀ i, 0 ≤ κ i) :
    (lpFiniteModes (Occ d)).subtype.comp
        (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))
      = (fockH hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by sorry
