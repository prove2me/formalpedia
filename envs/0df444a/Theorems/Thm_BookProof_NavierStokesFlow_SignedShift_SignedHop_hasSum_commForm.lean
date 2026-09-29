-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hasSum_commForm
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T10:05:27.686224+00:00
-- url     : https://prove2.me/theorems/2eb0077b-3731-4064-9e33-6eececa73a9a
-- title:
--   (x : maxDom sym) : HasSum (fun β => 2 * S.step * (S.amp β * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β) * ((x : L2I ι) : ι → ℂ) (S.shift β)).re)) (commForm (hopH S) (diagMax sym) x)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hasSum_commForm (x : maxDom sym) :
    HasSum (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
            * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (commForm (hopH S) (diagMax sym) x) := by sorry
