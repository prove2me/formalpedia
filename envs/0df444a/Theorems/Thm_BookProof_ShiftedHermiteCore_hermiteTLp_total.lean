-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_hermiteTLp_total
-- name    : BookProof.ShiftedHermiteCore.hermiteTLp_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:15:53.679619+00:00
-- url     : https://prove2.me/theorems/0226bc2c-2699-4fc4-87b0-ee109ab107d0
-- title:
--   The Lean 4 theorem `hermiteTLp_total` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteTLp_total` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.hermiteTLp_total
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

theorem BookProof.ShiftedHermiteCore.hermiteTLp_total (a k : Vd d) (v : L2d d)
    (h : ∀ α, (inner ℂ (hermiteTLp (d := d) a k α) v : ℂ) = 0) : v = 0 := by sorry
