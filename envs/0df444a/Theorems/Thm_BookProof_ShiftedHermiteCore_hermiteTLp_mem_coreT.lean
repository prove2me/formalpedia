-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_mem_coreT
-- name    : BookProof.ShiftedHermiteCore.hermiteTLp_mem_coreT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:14.398714+00:00
-- url     : https://prove2.me/theorems/f56ef98a-5e20-47f5-9255-e96363006d3c
-- title:
--   The Lean 4 theorem `hermiteTLp_mem_coreT` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteTLp_mem_coreT` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.hermiteTLp_mem_coreT
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedHermiteCore










open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedHermiteCore.hermiteTLp_mem_coreT (a k : Vd d) (α : Fin d →₀ ℕ) :
    hermiteTLp a k α ∈ polyGaussCoreT a k := by sorry
