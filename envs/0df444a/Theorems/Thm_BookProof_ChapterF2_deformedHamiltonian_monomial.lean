-- Prove2me | Theorems.Thm_BookProof_ChapterF2_deformedHamiltonian_monomial
-- name    : BookProof.ChapterF2.deformedHamiltonian_monomial
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:47:08.242503+00:00
-- url     : https://prove2.me/theorems/bbf775e3-ddc1-416d-b666-b420168526c5
-- title:
--   `BookProof.ChapterF2.deformedHamiltonian_monomial` (c : ℂ) (n : ℕ) : deformedHamiltonian c (X ^ n) = (c * n) • X ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF2`.
--
--   `BookProof.ChapterF2.deformedHamiltonian_monomial` (c : ℂ) (n : ℕ) : deformedHamiltonian c (X ^ n) = (c * n) • X ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF2.deformedHamiltonian_monomial`.

-- Generated from ChapterF2.lean — theorem BookProof.ChapterF2.deformedHamiltonian_monomial
import Definitions.Def_ChapterF1
import Mathlib
import Definitions.Def_ChapterF2
import Definitions.Def_ChapterGhostField
open BookProof.GhostField
open BookProof.ChapterF2


open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

theorem BookProof.ChapterF2.deformedHamiltonian_monomial (c : ℂ) (n : ℕ) :
    deformedHamiltonian c (X ^ n) = (c * n) • X ^ n := by sorry
