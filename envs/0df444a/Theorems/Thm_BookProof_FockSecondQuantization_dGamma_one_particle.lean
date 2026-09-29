-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_one_particle
-- name    : BookProof.FockSecondQuantization.dGamma_one_particle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:56:50.903178+00:00
-- url     : https://prove2.me/theorems/2a89fd45-9326-4e15-8194-dc34ed4d2e24
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) : dGamma col (Finsupp.single (Finsupp.single k 1) 1) = ∑ j ∈ (col k).support, (col k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_one_particle` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_one_particle
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGamma_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma col (Finsupp.single (Finsupp.single k 1) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ) := by sorry
