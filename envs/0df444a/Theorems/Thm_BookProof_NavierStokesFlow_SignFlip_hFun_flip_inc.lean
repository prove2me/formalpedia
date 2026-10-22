-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_hFun_flip_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.hFun_flip_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T09:24:37.461991+00:00
-- url     : https://prove2.me/theorems/66eca651-6859-406d-9e8f-33f351c82459
-- title:
--   The Lean 4 theorem `hFun_flip` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hFun_flip` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_hFun_flip`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.hFun_flip_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.hFun_flip_inc (S : ShiftData ι) (p : ι → ℕ) (k : ℕ)
    (hp : ∀ β, p (S.shift β) = p β + k) (X : ι → ℂ) (β : ι) :
    S.hFun (flipFun p X) β = (-1 : ℂ) ^ k * ((-1 : ℂ) ^ p β * S.hFun X β) := by sorry
