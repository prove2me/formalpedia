-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_fockH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T22:17:45.856185+00:00
-- url     : https://prove2.me/theorems/e3b3cb4f-0fe0-4541-852c-c6e131ce8447
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) : EssentiallySelfAdjointOn (lpFiniteModes (Occ d)) ((fockH hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.fockH_essentiallySelfAdjointOn_core (hκ : ∀ i, 0 ≤ κ i) :
    EssentiallySelfAdjointOn (lpFiniteModes (Occ d))
      ((fockH hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ)))) := by sorry
