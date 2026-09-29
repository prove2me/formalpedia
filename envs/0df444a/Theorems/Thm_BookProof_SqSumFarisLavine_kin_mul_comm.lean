-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_kin_mul_comm
-- name    : BookProof.SqSumFarisLavine.kin_mul_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:23.34585+00:00
-- url     : https://prove2.me/theorems/0cb4b291-cd75-435d-b26e-36ca639502dc
-- title:
--   (c : Fin D → ℂ) (f p : MvPolynomial (Fin D) ℂ) : (∑ j : Fin D, c j • coreD j (coreD j (f * p))) - f * ∑ j : Fin D, c j • coreD j (coreD j p) = ∑ j : Fin D, c j • (pderiv j...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.kin_mul_comm` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.kin_mul_comm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.kin_mul_comm (c : Fin D → ℂ) (f p : MvPolynomial (Fin D) ℂ) :
    (∑ j : Fin D, c j • coreD j (coreD j (f * p))) - f * ∑ j : Fin D, c j • coreD j (coreD j p)
      = ∑ j : Fin D, c j • (pderiv j (pderiv j f) * p
          + (2 : ℂ) • (pderiv j f * coreD j p)) := by sorry
