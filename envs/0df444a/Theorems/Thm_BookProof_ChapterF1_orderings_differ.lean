-- Prove2me | Theorems.Thm_BookProof_ChapterF1_orderings_differ
-- name    : BookProof.ChapterF1.orderings_differ
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:46:07.803665+00:00
-- url     : https://prove2.me/theorems/7771422d-cd3a-46bc-9420-ef7f9fcb6441
-- title:
--   `BookProof.ChapterF1.orderings_differ` : hamiltonian (1 : ℂ[X]) ≠ hamiltonianSym (1 : ℂ[X])
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF1`.
--
--   `BookProof.ChapterF1.orderings_differ` : hamiltonian (1 : ℂ[X]) ≠ hamiltonianSym (1 : ℂ[X])
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF1.orderings_differ`.

-- Generated from ChapterF1.lean — theorem BookProof.ChapterF1.orderings_differ
import Mathlib
import Definitions.Def_ChapterF1
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.ChapterF1


open Polynomial Finset
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF1.orderings_differ : hamiltonian (1 : ℂ[X]) ≠ hamiltonianSym (1 : ℂ[X]) := by sorry
