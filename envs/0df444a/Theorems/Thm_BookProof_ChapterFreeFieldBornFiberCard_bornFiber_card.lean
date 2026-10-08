-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberCard_bornFiber_card
-- name    : BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T11:40:01.31101+00:00
-- url     : https://prove2.me/theorems/75950648-451e-4f64-9ae0-e0b371e7d01c
-- title:
--   `BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card` {p : ↥(stdSimplex ℝ (Fin n))} (hp : ∀ k, 0 < (p : Fin n → ℝ) k) : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberCard`.
--
--   `BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card` {p : ↥(stdSimplex ℝ (Fin n))} (hp : ∀ k, 0 < (p : Fin n → ℝ) k) : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card`.

-- Generated from ChapterFreeFieldBornFiberCard.lean — theorem BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBornQuotient
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberCard
open BookProof.ChapterFreeFieldBornFiberCard

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignFiber BookProof.ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornQuotient

theorem BookProof.ChapterFreeFieldBornFiberCard.bornFiber_card {p : ↥(stdSimplex ℝ (Fin n))}
    (hp : ∀ k, 0 < (p : Fin n → ℝ) k) :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ n := by sorry
