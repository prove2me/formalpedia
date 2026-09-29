-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_pderiv_potPoly
-- name    : BookProof.SqSumFarisLavine.pderiv_potPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:53:59.037373+00:00
-- url     : https://prove2.me/theorems/68300cf7-e808-4b12-a323-f0765c328d29
-- title:
--   (v : R → Fin D → ℝ) (k : Fin D) : pderiv k (potPoly v) = gradPoly v k
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.pderiv_potPoly` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.pderiv_potPoly
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.pderiv_potPoly (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (potPoly v) = gradPoly v k := by sorry
