-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_inner_hermiteTLp
-- name    : BookProof.ShiftedHermiteCore.inner_hermiteTLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:25.776144+00:00
-- url     : https://prove2.me/theorems/a49072bc-7bcc-49f2-88b3-348173defa6a
-- title:
--   The Lean 4 theorem `inner_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_hermiteTLp` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.inner_hermiteTLp
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

theorem BookProof.ShiftedHermiteCore.inner_hermiteTLp (a k : Vd d) (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTLp a k α) (hermiteTLp a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by sorry
