-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_esgn_mul_shear_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.esgn_mul_shear_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:23:49.018458+00:00
-- url     : https://prove2.me/theorems/32d833ad-ec70-4849-8fad-780b70623656
-- title:
--   The Lean 4 theorem `esgn_mul_shear` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `esgn_mul_shear` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_esgn_mul_shear`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.esgn_mul_shear_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.esgn_mul_shear_inc (c : ℝ) (n : ℕ) :
    esgn c * ((shear |c| n : ℝ) : ℂ) = ((shear c n : ℝ) : ℂ) := by sorry
