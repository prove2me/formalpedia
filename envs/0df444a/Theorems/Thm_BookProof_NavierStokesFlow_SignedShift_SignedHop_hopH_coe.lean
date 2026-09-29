-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_coe
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:18:41.226338+00:00
-- url     : https://prove2.me/theorems/f44cc020-da01-46ec-aa87-e7a96f1ccae8
-- title:
--   (x : maxDom sym) (β : ι) : ((hopH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_coe` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hopH_coe (x : maxDom sym) (β : ι) :
    ((hopH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β := by sorry
