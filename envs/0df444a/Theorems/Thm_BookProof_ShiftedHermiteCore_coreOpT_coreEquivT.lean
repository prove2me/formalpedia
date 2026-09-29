-- Prove2me | Theorems.Thm_BookProof_ShiftedHermiteCore_coreOpT_coreEquivT
-- name    : BookProof.ShiftedHermiteCore.coreOpT_coreEquivT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:11:18.947688+00:00
-- url     : https://prove2.me/theorems/de833b9b-7d2a-4072-b4e1-e8e3c36c49a7
-- title:
--   The Lean 4 theorem `coreOpT_coreEquivT` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOpT_coreEquivT` in the `ChapterShiftedHermiteCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
-- Generated from ChapterShiftedHermiteCore.lean — theorem BookProof.ShiftedHermiteCore.coreOpT_coreEquivT
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

theorem BookProof.ShiftedHermiteCore.coreOpT_coreEquivT (a k : Vd d) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : coreOpT a k T (coreEquivT a k p) = coreEquivT a k (T p) := by sorry
