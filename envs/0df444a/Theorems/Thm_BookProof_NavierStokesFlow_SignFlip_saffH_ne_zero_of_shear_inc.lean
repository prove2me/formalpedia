-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_saffH_ne_zero_of_shear_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.saffH_ne_zero_of_shear_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T08:10:32.708206+00:00
-- url     : https://prove2.me/theorems/82a3375a-1ca3-4a41-8fe5-93e6bdb59fb7
-- title:
--   The Lean 4 theorem `saffH_ne_zero_of_shear` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `saffH_ne_zero_of_shear` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_saffH_ne_zero_of_shear`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.saffH_ne_zero_of_shear_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
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

theorem BookProof.NavierStokesFlow.SignFlip.saffH_ne_zero_of_shear_inc {κ : ℝ} (hκ : 0 ≤ κ) {c : ℝ} (hc : c ≠ 0) :
    saffH hκ c (basisState κ |c| 0) ≠ 0 := by sorry
