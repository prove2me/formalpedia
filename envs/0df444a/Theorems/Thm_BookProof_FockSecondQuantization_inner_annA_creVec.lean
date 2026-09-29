-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_annA_creVec
-- name    : BookProof.FockSecondQuantization.inner_annA_creVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:21:21.970383+00:00
-- url     : https://prove2.me/theorems/7f66c030-d362-4550-9a27-0eac7fb3c9dd
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ} (h : (col j).support ⊆ L) : (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ) = ∑ k ∈ L, (col j) k *...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_annA_creVec` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_annA_creVec
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_annA_creVec (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by sorry
