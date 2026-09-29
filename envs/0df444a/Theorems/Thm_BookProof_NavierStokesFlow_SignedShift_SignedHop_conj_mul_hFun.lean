-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_conj_mul_hFun
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_mul_hFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:17:58.313799+00:00
-- url     : https://prove2.me/theorems/e89d0e74-fbac-4eae-ae56-970cb96ce96b
-- title:
--   (X Y : ι → ℂ) (β : ι) : (starRingEnd ℂ) (X β) * S.hFun Y β = -Complex.I * S.crossA X Y β + Complex.I * S.maj.hop (S.crossB X Y) β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_mul_hFun` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_mul_hFun
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_mul_hFun (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (X β) * S.hFun Y β
      = -Complex.I * S.crossA X Y β + Complex.I * S.maj.hop (S.crossB X Y) β := by sorry
