-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_kin_kin_comm
-- name    : BookProof.SqSumFarisLavine.kin_kin_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:51:36.080009+00:00
-- url     : https://prove2.me/theorems/b4fce2a3-dd77-4370-b34c-98a82a07286d
-- title:
--   (c : Fin D → ℂ) (p : MvPolynomial (Fin D) ℂ) : (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p)))) = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D,...
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.kin_kin_comm` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.kin_kin_comm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.kin_kin_comm (c : Fin D → ℂ) (p : MvPolynomial (Fin D) ℂ) :
    (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p))))
      = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D, coreD k (coreD k p))) := by sorry
