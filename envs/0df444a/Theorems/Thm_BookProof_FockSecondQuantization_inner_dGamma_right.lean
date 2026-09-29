-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_dGamma_right
-- name    : BookProof.FockSecondQuantization.inner_dGamma_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:24.815122+00:00
-- url     : https://prove2.me/theorems/0f47ebee-daa1-486e-86dc-b02fe8b44bf2
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ} (hv : modes v ⊆ L) (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) : (inner ℂ (toLp u) (toLp (dGamma col v)) :...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_dGamma_right` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_dGamma_right
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_dGamma_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hv : modes v ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (dGamma col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by sorry
