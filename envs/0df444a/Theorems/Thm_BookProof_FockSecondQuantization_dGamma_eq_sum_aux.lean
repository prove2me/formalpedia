-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum_aux
-- name    : BookProof.FockSecondQuantization.dGamma_eq_sum_aux
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:15:25.853988+00:00
-- url     : https://prove2.me/theorems/a31d3e97-311f-4018-ad54-b2e360788462
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) : ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_eq_sum_aux` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_eq_sum_aux
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGamma_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by sorry
