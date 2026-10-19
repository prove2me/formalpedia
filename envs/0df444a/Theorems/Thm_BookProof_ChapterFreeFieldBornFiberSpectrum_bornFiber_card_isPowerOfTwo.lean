-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_isPowerOfTwo
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:45.459438+00:00
-- url     : https://prove2.me/theorems/465239d0-358a-4d55-8f7c-e33be2c17d3f
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo` {p : ↥(stdSimplex ℝ (Fin n))} : ∃ k, 1 ≤ k ∧ k ≤ n ∧ Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo` {p : ↥(stdSimplex ℝ (Fin n))} : ∃ k, 1 ≤ k ∧ k ≤ n ∧ Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo
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

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_isPowerOfTwo {p : ↥(stdSimplex ℝ (Fin n))} :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ k := by sorry
