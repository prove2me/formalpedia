-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberBounds_bornFiber_card_le_two_pow_n
-- name    : BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:43.879984+00:00
-- url     : https://prove2.me/theorems/6ac7fe3d-b368-471d-b571-e913ab272bcd
-- title:
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberBounds`.
--
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n`.

-- Generated from ChapterFreeFieldBornFiberBounds.lean — theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberBounds


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_le_two_pow_n {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n := by sorry
