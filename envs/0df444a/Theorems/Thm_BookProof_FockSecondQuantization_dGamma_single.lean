-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_single
-- name    : BookProof.FockSecondQuantization.dGamma_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:55:42.128422+00:00
-- url     : https://prove2.me/theorems/3b4e635a-72d2-4c8a-a081-da4f78d8fd58
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) : dGamma col (Finsupp.single β c) = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1))
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_single` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_single
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGamma_single (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) :
    dGamma col (Finsupp.single β c)
      = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)) := by sorry
