-- Prove2me | Theorems.Thm_BookProof_ChapterF2_massGap_smallest_excited
-- name    : BookProof.ChapterF2.massGap_smallest_excited
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:48:05.29184+00:00
-- url     : https://prove2.me/theorems/598592b0-c478-47d8-bda4-554e7ada0b92
-- title:
--   `BookProof.ChapterF2.massGap_smallest_excited` (n : ℕ) (hn : n ≠ 0) : hamiltonian (X ^ n) = (n : ℂ) • X ^ n ∧ (1 : ℕ) ≤ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF2`.
--
--   `BookProof.ChapterF2.massGap_smallest_excited` (n : ℕ) (hn : n ≠ 0) : hamiltonian (X ^ n) = (n : ℂ) • X ^ n ∧ (1 : ℕ) ≤ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF2.massGap_smallest_excited`.

-- Generated from ChapterF2.lean — theorem BookProof.ChapterF2.massGap_smallest_excited
import Definitions.Def_ChapterF1
import Mathlib
import Definitions.Def_ChapterF2
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.ChapterF2


open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

theorem BookProof.ChapterF2.massGap_smallest_excited (n : ℕ) (hn : n ≠ 0) :
    hamiltonian (X ^ n) = (n : ℂ) • X ^ n ∧ (1 : ℕ) ≤ n := by sorry
