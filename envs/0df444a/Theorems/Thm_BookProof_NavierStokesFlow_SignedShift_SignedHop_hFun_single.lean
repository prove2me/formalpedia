-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hFun_single
-- name    : BookProof.NavierStokesFlow.SignedShift.SignedHop.hFun_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:00:49.071985+00:00
-- url     : https://prove2.me/theorems/e9f89ad3-59fe-47ee-a2f5-4e11d0a70b52
-- title:
--   [DecidableEq ι] {sym : ι → ℝ} (S : SignedHop ι sym) {X : ι → ℂ} {o : ι} (hX : ∀ α, X α = if α = o then 1 else 0) (γ : ι) : S.hFun X γ = Complex.I * ((if γ = S.shift o then (S.amp o : ℂ) else 0) -...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SignedShift.SignedHop.hFun_single` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSignedShift.lean — theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hFun_single
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow.SignedShift.SignedHop









open scoped ENNReal




variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

theorem BookProof.NavierStokesFlow.SignedShift.SignedHop.hFun_single [DecidableEq ι] {sym : ι → ℝ} (S : SignedHop ι sym)
    {X : ι → ℂ} {o : ι} (hX : ∀ α, X α = if α = o then 1 else 0) (γ : ι) :
    S.hFun X γ = Complex.I * ((if γ = S.shift o then (S.amp o : ℂ) else 0)
      - (if S.shift γ = o then (S.amp γ : ℂ) else 0)) := by sorry
