-- Prove2me | Theorems.Thm_BookProof_SqSumFarisLavine_core_eq_pgLp
-- name    : BookProof.SqSumFarisLavine.core_eq_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T11:47:33.926924+00:00
-- url     : https://prove2.me/theorems/c1aec7ca-245d-46fa-9b0e-a4b871a9c552
-- title:
--   (u : polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.SqSumFarisLavine.core_eq_pgLp` (module `BookProof.SqSumFarisLavine`), source chapter `BookProof/ChapterSqSumFarisLavine.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

-- Generated from ChapterSqSumFarisLavine.lean — theorem BookProof.SqSumFarisLavine.core_eq_pgLp
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine












open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

theorem BookProof.SqSumFarisLavine.core_eq_pgLp (u : polyGaussCore (d := D)) :
    ∃ p : MvPolynomial (Fin D) ℂ, u = ⟨pgLp p, pgLp_mem_core p⟩ := by sorry
