-- Prove2me | Theorems.Thm_BookProof_ChapterPvmMeasure_Pvm_add_of_disjoint
-- name    : BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:57:58.144+00:00
-- url     : https://prove2.me/theorems/6dd82ee9-303f-40fb-9215-727dd90928eb
-- title:
--   `BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint` {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (hd : Disjoint E F) (u : H) : P.p (E ∪ F) u = P.p E u + P.p F u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmMeasure`.
--
--   `BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint` {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F) (hd : Disjoint E F) (u : H) : P.p (E ∪ F) u = P.p E u + P.p F u
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint`.

-- Generated from ChapterPvmMeasure.lean — theorem BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint
import Mathlib
import Definitions.Def_ChapterPvmMeasure
open BookProof.ChapterPvmMeasure
open BookProof.ChapterPvmMeasure


open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (P : Pvm X H)

theorem BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u : H) : P.p (E ∪ F) u = P.p E u + P.p F u := by sorry
