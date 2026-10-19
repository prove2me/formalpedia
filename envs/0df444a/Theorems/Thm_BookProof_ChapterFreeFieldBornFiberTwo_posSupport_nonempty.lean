-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_posSupport_nonempty
-- name    : BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:28:13.336978+00:00
-- url     : https://prove2.me/theorems/945eef98-820d-478c-8cfe-c49c24c68a9d
-- title:
--   `BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : (posSupport p).Nonempty
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberTwo`.
--
--   `BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty` {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) : (posSupport p).Nonempty
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty`.

-- Generated from ChapterFreeFieldBornFiberTwo.lean — theorem BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty
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

theorem BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    (posSupport p).Nonempty := by sorry
