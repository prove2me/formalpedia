-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_mode_hamiltonian_eq
-- name    : BookProof.NavierStokesFlow.FockCanonical.mode_hamiltonian_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T07:53:19.177987+00:00
-- url     : https://prove2.me/theorems/dff08941-09ed-438e-a9ca-1e1233a683a1
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) : (lpFiniteModes (Occ d)).subtype.comp (((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i))) = (ShiftData.shiftH (modeData hκ...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.mode_hamiltonian_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.mode_hamiltonian_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.Bosonic
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

theorem BookProof.NavierStokesFlow.FockCanonical.mode_hamiltonian_eq (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) :
    (lpFiniteModes (Occ d)).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))
      = (ShiftData.shiftH (modeData hκ i)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by sorry
