-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_left
-- name    : BookProof.FockSecondQuantization.inner_dGamma_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:21:54.996488+00:00
-- url     : https://prove2.me/theorems/6e508e8f-a24f-4626-9d51-1e0efad3a32c
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ} (hu : modes u ⊆ L) (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) : (inner ℂ (toLp (dGamma col u)) (toLp v) :...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_dGamma_left` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_dGamma_left
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_dGamma_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hu : modes u ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by sorry
