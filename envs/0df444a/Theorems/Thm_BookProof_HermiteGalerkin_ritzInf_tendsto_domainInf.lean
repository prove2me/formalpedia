-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_ritzInf_tendsto_domainInf
-- name    : BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:11.060533+00:00
-- url     : https://prove2.me/theorems/81c59772-0aef-4688-a1be-fd8fa82850ed
-- title:
--   The Lean 4 theorem `ritzInf_tendsto_domainInf` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritzInf_tendsto_domainInf` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}

theorem BookProof.HermiteGalerkin.ritzInf_tendsto_domainInf (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) :
    Tendsto (fun m : ℕ => ritzInf H (galerkinSpan b (m + 1))) atTop
      (nhds (ritzInf H (finiteModeDomain b))) := by sorry
