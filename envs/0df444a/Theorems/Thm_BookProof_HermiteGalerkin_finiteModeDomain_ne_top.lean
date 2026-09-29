-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_finiteModeDomain_ne_top
-- name    : BookProof.HermiteGalerkin.finiteModeDomain_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:30:27.423893+00:00
-- url     : https://prove2.me/theorems/1a1de6a5-ea3c-4e2e-ae5b-7432749d4abc
-- title:
--   The Lean 4 theorem `finiteModeDomain_ne_top` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModeDomain_ne_top` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.finiteModeDomain_ne_top
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







open scoped InnerProductSpace ENNReal

theorem BookProof.HermiteGalerkin.finiteModeDomain_ne_top : finiteModeDomain ell2Basis ≠ ⊤ := by sorry
