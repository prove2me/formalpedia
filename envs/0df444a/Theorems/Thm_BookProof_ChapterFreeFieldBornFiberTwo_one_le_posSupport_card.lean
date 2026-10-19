-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_one_le_posSupport_card
-- name    : BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:30:00.659986+00:00
-- url     : https://prove2.me/theorems/ccabbbf8-a394-4d68-9fa0-2efedcad2671
-- title:
--   `BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : 1 ≤ (posSupport p).card
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberTwo`.
--
--   `BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : 1 ≤ (posSupport p).card
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card`.

-- Generated from ChapterFreeFieldBornFiberTwo.lean — theorem BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card
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

theorem BookProof.ChapterFreeFieldBornFiberTwo.one_le_posSupport_card {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    1 ≤ (posSupport p).card := by sorry
