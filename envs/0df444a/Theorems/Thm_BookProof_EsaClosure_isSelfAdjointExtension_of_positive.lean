-- Prove2me | Theorems.Thm_BookProof_EsaClosure_isSelfAdjointExtension_of_positive
-- name    : BookProof.EsaClosure.isSelfAdjointExtension_of_positive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:43:18.306209+00:00
-- url     : https://prove2.me/theorems/a1c86fba-cf29-4898-af7d-13ad0a835dba
-- title:
--   The Lean 4 theorem `isSelfAdjointExtension_of_positive` in the `ChapterEsaClosure` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isSelfAdjointExtension_of_positive` in the `ChapterEsaClosure` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterEsaClosure.lean

-- Generated from ChapterEsaClosure.lean — theorem BookProof.EsaClosure.isSelfAdjointExtension_of_positive
import Mathlib
import Definitions.Def_ChapterEsaClosure
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure



open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open BookProof.YangMillsFriedrichs

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.EsaClosure.isSelfAdjointExtension_of_positive {D Dom : Submodule ℂ F} {H : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsPositiveSelfAdjointExtension H A) : IsSelfAdjointExtension H A := by sorry
