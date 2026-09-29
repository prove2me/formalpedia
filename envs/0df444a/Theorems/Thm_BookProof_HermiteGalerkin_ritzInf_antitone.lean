-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_ritzInf_antitone
-- name    : BookProof.HermiteGalerkin.ritzInf_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:09.417689+00:00
-- url     : https://prove2.me/theorems/07a8a7d3-1b54-471f-b2b6-681db42f88ca
-- title:
--   The Lean 4 theorem `ritzInf_antitone` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritzInf_antitone` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.ritzInf_antitone
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}

theorem BookProof.HermiteGalerkin.ritzInf_antitone (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    {V W : Submodule ℂ F} (hVW : V ≤ W) (hV : (ritzSet H V).Nonempty) :
    ritzInf H W ≤ ritzInf H V := by sorry
