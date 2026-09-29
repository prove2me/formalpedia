-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_ym_fock_friedrichs_extension
-- name    : BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:29:15.297021+00:00
-- url     : https://prove2.me/theorems/19b15e1d-eb4b-4785-9330-c13e9e6b5f0a
-- title:
--   (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.ym_fock_friedrichs_extension` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.ym_fock_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]











open Filter Topology
















open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

theorem BookProof.FockSecondQuantization.ym_fock_friedrichs_extension (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A := by sorry
