-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_even
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:35.523295+00:00
-- url     : https://prove2.me/theorems/d005d1aa-222f-4d71-a986-3f916802830c
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ∣ Nat.card ↥(bornMapSphere n ⁻¹' {p})
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ∣ Nat.card ↥(bornMapSphere n ⁻¹' {p})
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even
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

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_even {p : ↥(stdSimplex ℝ (Fin n))} :
    2 ∣ Nat.card ↥(bornMapSphere n ⁻¹' {p}) := by sorry
