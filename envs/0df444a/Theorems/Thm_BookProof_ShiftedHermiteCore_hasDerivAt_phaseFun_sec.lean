-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_hasDerivAt_phaseFun_sec
-- name    : BookProof.ShiftedHermiteCore.hasDerivAt_phaseFun_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:14:15.590532+00:00
-- url     : https://prove2.me/theorems/4b8b8ed6-4d7e-4f9d-a782-2005cc5170ae
-- title:
--   The Lean 4 theorem `hasDerivAt_phaseFun_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_phaseFun_sec` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.hasDerivAt_phaseFun_sec
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

theorem BookProof.ShiftedHermiteCore.hasDerivAt_phaseFun_sec (k x : Vd d) (i : Fin d) :
    HasDerivAt (fun t : ℝ => phaseFun k (sec i x t))
      (phaseFun k x * (Complex.I * ((k i : ℝ) : ℂ))) (x i) := by sorry
