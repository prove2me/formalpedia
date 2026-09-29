-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_finiteModeRestrict_hypotheses
-- name    : BookProof.HermiteGalerkin.finiteModeRestrict_hypotheses
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:30:46.093333+00:00
-- url     : https://prove2.me/theorems/ad81ca86-499a-4a96-b320-23054ab17536
-- title:
--   The Lean 4 theorem `finiteModeRestrict_hypotheses` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModeRestrict_hypotheses` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.finiteModeRestrict_hypotheses
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]









variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]










variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HermiteGalerkin.finiteModeRestrict_hypotheses (A₀ : F →L[ℂ] F) (hsa : IsSelfAdjoint A₀)
    (hposA : ∀ u : F, 0 ≤ (inner ℂ u (A₀ u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) :
    SymmetricOn (finiteModeDomain b) (finiteModeRestrict A₀ b) ∧
      (∀ x : finiteModeDomain b, 0 ≤ quadForm (finiteModeRestrict A₀ b) x) ∧
      (∀ x : finiteModeDomain b, ‖finiteModeRestrict A₀ b x‖ ≤ ‖A₀‖ * ‖(x : F)‖) := by sorry
