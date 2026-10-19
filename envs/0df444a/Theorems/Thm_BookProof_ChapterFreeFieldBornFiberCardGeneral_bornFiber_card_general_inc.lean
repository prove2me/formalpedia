-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberCardGeneral_bornFiber_card_general_inc
-- name    : BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T20:14:23.872246+00:00
-- url     : https://prove2.me/theorems/10fbe3f4-7439-4226-923a-65337befc3e8
-- title:
--   `BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport (p : Fin n → ℝ)).card
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberCardGeneral`.
--
--   `BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc` {p : ↥(stdSimplex ℝ (Fin n))} : Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport (p : Fin n → ℝ)).card
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc`.
--
--   Replaces the unuploadable node `BookProof_ChapterFreeFieldBornFiberCardGeneral_bornFiber_card_general`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFreeFieldBornFiberCardGeneral.lean — theorem BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCard
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberCardGeneral


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignFiber BookProof.ChapterFreeFieldBornSectionBij
open BookProof.ChapterFreeFieldBornQuotient BookProof.ChapterFreeFieldBornFiberCard


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberCardGeneral.bornFiber_card_general_inc {p : ↥(stdSimplex ℝ (Fin n))} :
    Nat.card ↥(bornMapSphere n ⁻¹' {p}) = 2 ^ (posSupport (p : Fin n → ℝ)).card := by sorry
