-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_achievable_iff
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:41.354053+00:00
-- url     : https://prove2.me/theorems/f495a80f-5a78-46e0-a51f-28ff8b314079
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff` {c : ℕ} : (∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p}) = c) ↔ ∃ k, 1 ≤ k ∧...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff` {c : ℕ} : (∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p}) = c) ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ c = 2 ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBornFiberBounds
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
open BookProof.ChapterFreeFieldBornFiberSpectrum


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_achievable_iff {c : ℕ} :
    (∃ p : ↥(stdSimplex ℝ (Fin n)), Nat.card ↥(bornMapSphere n ⁻¹' {p}) = c) ↔
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ c = 2 ^ k := by sorry
