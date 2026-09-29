-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_orthonormal_hermiteTLp
-- name    : BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:17.158805+00:00
-- url     : https://prove2.me/theorems/9470ee0d-adf9-46b7-9518-28ee54629e0f
-- title:
--   The Lean 4 theorem `orthonormal_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `orthonormal_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp
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

theorem BookProof.ShiftedHermiteCore.orthonormal_hermiteTLp (a k : Vd d) : Orthonormal ℂ (hermiteTLp (d := d) a k) := by sorry
