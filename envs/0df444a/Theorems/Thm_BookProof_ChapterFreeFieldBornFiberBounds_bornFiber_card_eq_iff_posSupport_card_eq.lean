-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberBounds_bornFiber_card_eq_iff_posSupport_card_eq
-- name    : BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:53.185431+00:00
-- url     : https://prove2.me/theorems/134e45d3-7328-4e5b-ba4d-379a8090099c
-- title:
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq` {p q : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = Nat.card ↥(bornMapSpher
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberBounds`.
--
--   `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq` {p q : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = Nat.card ↥(bornMapSphere n ⁻¹' {q}) ↔ (posSupport (p : Fin n → ℝ)).card = (posSupport (q : Fin n → ℝ)).card
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq`.

-- Generated from ChapterFreeFieldBornFiberBounds.lean — theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq
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

theorem BookProof.ChapterFreeFieldBornFiberBounds.bornFiber_card_eq_iff_posSupport_card_eq
    {p q : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = Nat.card ↥(bornMapSphere n ⁻¹' {q}) ↔
      (posSupport (p : Fin n → ℝ)).card = (posSupport (q : Fin n → ℝ)).card := by sorry
