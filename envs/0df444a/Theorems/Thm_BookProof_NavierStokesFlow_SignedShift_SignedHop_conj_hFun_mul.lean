-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_conj_hFun_mul
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_hFun_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T09:17:24.151464+00:00
-- url     : https://prove2.me/theorems/46337653-8ecc-4851-8087-4a22708d81d9
-- title:
--   (X Y : ι → ℂ) (β : ι) : (starRingEnd ℂ) (S.hFun X β) * Y β = -Complex.I * S.maj.hop (S.crossA X Y) β + Complex.I * S.crossB X Y β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_hFun_mul` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_hFun_mul
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.conj_hFun_mul (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (S.hFun X β) * Y β
      = -Complex.I * S.maj.hop (S.crossA X Y) β + Complex.I * S.crossB X Y β := by sorry
