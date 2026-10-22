-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_saffH_coord_succ_succ_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.saffH_coord_succ_succ_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:25:29.192987+00:00
-- url     : https://prove2.me/theorems/931ab2d5-e5b9-4f5f-8f8d-851f3b04440e
-- title:
--   The Lean 4 theorem `saffH_coord_succ_succ` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `saffH_coord_succ_succ` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_saffH_coord_succ_succ`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.saffH_coord_succ_succ_inc
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

theorem BookProof.NavierStokesFlow.SignFlip.saffH_coord_succ_succ_inc {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) (n : ℕ) :
    ((saffH hκ c (basisState κ |c| n) : L2I ℕ) : ℕ → ℂ) (n + 2)
      = Complex.I * ((amp κ n : ℝ) : ℂ) := by sorry
