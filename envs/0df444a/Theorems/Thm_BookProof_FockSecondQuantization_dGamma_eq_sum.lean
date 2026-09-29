-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum
-- name    : BookProof.FockSecondQuantization.dGamma_eq_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:21:10.666114+00:00
-- url     : https://prove2.me/theorems/d2c9a78d-9f9e-4ebf-b657-554d91c28a5d
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) : dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_eq_sum` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_eq_sum
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGamma_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by sorry
