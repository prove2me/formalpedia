-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberBounds_bornFiber_card_bounds
-- name    : BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:28:29.37923+00:00
-- url     : https://prove2.me/theorems/abc90251-a55d-4deb-b3e4-6485ed0a1665
-- title:
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∧ Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberBounds`.
--
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∧ Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds`.

-- Generated from ChapterFreeFieldBornFiberBounds.lean — theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds
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

theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_bounds {p : ↥(stdSimplex ℝ (Fin n))} :
    2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p}) ∧
      Nat.card ↥(bornMapSphere n ⁻¹' {p}) ≤ 2 ^ n := by sorry
