-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_coreD_sum
-- name    : BookProof.SqSumFarisLavine.coreD_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:48:09.347123+00:00
-- url     : https://prove2.me/theorems/9d55c092-91fb-4dc3-9f7f-386fe8dcc5bd
-- title:
--   {ι : Type*} (s : Finset ι) (j : Fin D) (f : ι → MvPolynomial (Fin D) ℂ) : coreD j (∑ i ∈ s, f i) = ∑ i ∈ s, coreD j (f i)
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.coreD_sum` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.coreD_sum
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.coreD_sum {ι : Type*} (s : Finset ι) (j : Fin D) (f : ι → MvPolynomial (Fin D) ℂ) :
    coreD j (∑ i ∈ s, f i) = ∑ i ∈ s, coreD j (f i) := by sorry
