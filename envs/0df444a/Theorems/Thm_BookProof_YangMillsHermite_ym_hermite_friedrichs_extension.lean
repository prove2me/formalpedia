-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_ym_hermite_friedrichs_extension
-- name    : BookProof.YangMillsHermite.ym_hermite_friedrichs_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:30:15.880644+00:00
-- url     : https://prove2.me/theorems/7c5f468b-b763-4ec7-84b2-ef76c8ea9cbf
-- title:
--   (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99), IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) fabc) A
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.ym_hermite_friedrichs_extension` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.ym_hermite_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

















































variable {D : Submodule ℂ (L2d d)}












variable {D : Submodule ℂ (L2d 99)}

theorem BookProof.YangMillsHermite.ym_hermite_friedrichs_extension (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ (Dom : Submodule ℂ (L2d 99)) (A : Dom →ₗ[ℂ] L2d 99),
      IsPositiveSelfAdjointExtension (ymHamiltonian (coreRepPoly 99) fabc) A := by sorry
