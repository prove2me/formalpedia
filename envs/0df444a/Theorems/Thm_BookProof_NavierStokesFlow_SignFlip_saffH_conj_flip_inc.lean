-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_saffH_conj_flip_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.saffH_conj_flip_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:25:06.644767+00:00
-- url     : https://prove2.me/theorems/2531d3e1-2a7a-432e-990d-c4ea2f808260
-- title:
--   The Lean 4 theorem `saffH_conj_flip` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `saffH_conj_flip` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_saffH_conj_flip`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.saffH_conj_flip_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
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

theorem BookProof.NavierStokesFlow.SignFlip.saffH_conj_flip_inc {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c < 0)
    (x : maxDom (oscSymbol (affMu κ |c|))) :
    (flipU (fun n : ℕ => n) (affH hκ (abs_nonneg c) x) : L2I ℕ)
      = (saffH hκ c ⟨flipU (fun n : ℕ => n) (x : L2I ℕ),
          flipU_mem_maxDom _ (oscSymbol (affMu κ |c|)) x.2⟩ : L2I ℕ) := by sorry
