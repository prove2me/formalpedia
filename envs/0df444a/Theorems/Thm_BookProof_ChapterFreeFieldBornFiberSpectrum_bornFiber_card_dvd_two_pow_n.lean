-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberSpectrum_bornFiber_card_dvd_two_pow_n
-- name    : BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:10.942776+00:00
-- url     : https://prove2.me/theorems/1a1b3dda-d5be-47f5-bd30-dec10704496e
-- title:
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∣ 2 ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberSpectrum`.
--
--   `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∣ 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n`.

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n
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

theorem BookProof.ChapterFreeFieldBornFiberSpectrum.bornFiber_card_dvd_two_pow_n {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∣ 2 ^ n := by sorry
