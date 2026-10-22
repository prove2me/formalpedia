-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_sblockFun_embFun_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.sblockFun_embFun_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T08:11:09.963982+00:00
-- url     : https://prove2.me/theorems/0f358116-3244-4aa8-b57e-1468c9f80e1b
-- title:
--   The Lean 4 theorem `sblockFun_embFun` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sblockFun_embFun` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_sblockFun_embFun`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.sblockFun_embFun_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesBilinearEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}
variable {J : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.sblockFun_embFun_inc (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (j : J) (a : ℕ → ℂ) :
    sblockFun κ c hκ (embFun j a)
      = embFun j (fun n => (affData (hκ j) (abs_nonneg (c j))).fst.hFun a n
          + esgn (c j) * (affData (hκ j) (abs_nonneg (c j))).snd.hFun a n) := by sorry
