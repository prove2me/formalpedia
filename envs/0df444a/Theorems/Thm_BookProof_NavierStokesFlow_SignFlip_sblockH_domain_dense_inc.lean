-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignFlip_sblockH_domain_dense_inc
-- name    : BookProof.NavierStokesFlow.SignFlip.sblockH_domain_dense_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T08:11:11.905298+00:00
-- url     : https://prove2.me/theorems/27bae882-a1e8-4639-8b87-d30c7dbceafb
-- title:
--   The Lean 4 theorem `sblockH_domain_dense` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sblockH_domain_dense` in the `ChapterNavierStokesSignFlip` chapter of the timepiece formalization.
--
--   Replaces the unuploadable node `BookProof_NavierStokesFlow_SignFlip_sblockH_domain_dense`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSignFlip.lean

-- Generated from ChapterNavierStokesSignFlip.lean — theorem BookProof.NavierStokesFlow.SignFlip.sblockH_domain_dense_inc
import Mathlib
import Definitions.Def_ChapterNavierStokesSignFlip
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignFlip


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι : Type*}
variable {J : Type*}

theorem BookProof.NavierStokesFlow.SignFlip.sblockH_domain_dense_inc :
    Dense ((lpFiniteModes (ℕ × J) : Submodule ℂ (L2I (ℕ × J))) : Set (L2I (ℕ × J))) := by sorry
