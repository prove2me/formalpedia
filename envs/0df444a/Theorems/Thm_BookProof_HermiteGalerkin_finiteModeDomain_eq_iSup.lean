-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_finiteModeDomain_eq_iSup
-- name    : BookProof.HermiteGalerkin.finiteModeDomain_eq_iSup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:16.284357+00:00
-- url     : https://prove2.me/theorems/264b349b-b622-4ecf-9934-05bd09f9ea3e
-- title:
--   The Lean 4 theorem `finiteModeDomain_eq_iSup` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModeDomain_eq_iSup` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.finiteModeDomain_eq_iSup
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by sorry
