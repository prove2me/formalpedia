-- Prove2me | Theorems.Thm_BookProof_GaussCoreQuadBounds_norm_weighted_kin_le
-- name    : BookProof.GaussCoreQuadBounds.norm_weighted_kin_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:06:45.501259+00:00
-- url     : https://prove2.me/theorems/89e74a94-28b2-4240-95b9-4d8af942ecff
-- title:
--   {kappa : Fin D → ℝ} {km : ℝ} (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (p : MvPolynomial (Fin D) ℂ) : ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖ ≤...
-- statement:
--   Lean 4 theorem `BookProof.GaussCoreQuadBounds.norm_weighted_kin_le` (module `BookProof.GaussCoreQuadBounds`), source chapter `BookProof/ChapterGaussCoreQuadBounds.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterGaussCoreQuadBounds.lean

-- Generated from ChapterGaussCoreQuadBounds.lean — theorem BookProof.GaussCoreQuadBounds.norm_weighted_kin_le
import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.GaussCoreQuadBounds








open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine

noncomputable section

variable {D : ℕ}

theorem BookProof.GaussCoreQuadBounds.norm_weighted_kin_le {kappa : Fin D → ℝ} {km : ℝ} (hkm : 0 ≤ km)
    (hk : ∀ j, |kappa j| ≤ km) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖
      ≤ km * ‖pgLp (kinPoly p)‖ := by sorry
