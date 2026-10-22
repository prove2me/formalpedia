-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_deficiencyTrivialAt_sblockH_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.deficiencyTrivialAt_sblockH_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:23:11.804792+00:00
-- url     : https://prove2.me/theorems/81ec68b8-11eb-47cf-9c60-195bb87733ac
-- title:
--   The Lean 4 theorem `deficiencyTrivialAt_sblockH` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `deficiencyTrivialAt_sblockH` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_deficiencyTrivialAt_sblockH`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.deficiencyTrivialAt_sblockH_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}
variable {J : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.deficiencyTrivialAt_sblockH_inc (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (z : ℂ)
    (hblk : ∀ j, DeficiencyTrivialAt (lpFiniteModes ℕ)
      ((saffH (hκ j) (c j)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol (affMu (κ j) |c j|))))) z) :
    DeficiencyTrivialAt (lpFiniteModes (ℕ × J)) (sblockH κ c hκ) z := by sorry
