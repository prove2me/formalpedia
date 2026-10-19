-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberBounds_posSupport_card_le_n
-- name    : BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:29:00.696648+00:00
-- url     : https://prove2.me/theorems/7072a639-fe25-42dc-9695-c5964d94bdf0
-- title:
--   `BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n` {p : Fin n → ℝ} : (posSupport p).card ≤ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberBounds`.
--
--   `BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n` {p : Fin n → ℝ} : (posSupport p).card ≤ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n`.

-- Generated from ChapterFreeFieldBornFiberBounds.lean — theorem BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n
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

theorem BookProof.ChapterFreeFieldBornFiberBounds.posSupport_card_le_n {p : Fin n → ℝ} : (posSupport p).card ≤ n := by sorry
