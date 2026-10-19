-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_two_le_bornFiber_card
-- name    : BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:28:25.959985+00:00
-- url     : https://prove2.me/theorems/9102d024-b86b-4da2-8631-ab9e2ca1a564
-- title:
--   `BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p})
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberTwo`.
--
--   `BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card` {p : ↥(stdSimplex ℝ (Fin n))} : 2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p})
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card`.

-- Generated from ChapterFreeFieldBornFiberTwo.lean — theorem BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberTwo


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberTwo.two_le_bornFiber_card {p : ↥(stdSimplex ℝ (Fin n))} :
    2 ≤ Nat.card ↥(bornMapSphere n ⁻¹' {p}) := by sorry
