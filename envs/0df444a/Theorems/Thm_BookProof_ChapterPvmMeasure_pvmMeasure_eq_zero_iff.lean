-- Prove2me | Theorems.Thm_BookProof_ChapterPvmMeasure_pvmMeasure_eq_zero_iff
-- name    : BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:59:34.780979+00:00
-- url     : https://prove2.me/theorems/62e90887-42bf-4df4-89c0-7baf5961fbb4
-- title:
--   `BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff` {E : Set X} (hE : MeasurableSet E) : pvmMeasure P ψ E = 0 ↔ P.p E ψ = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmMeasure`.
--
--   `BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff` {E : Set X} (hE : MeasurableSet E) : pvmMeasure P ψ E = 0 ↔ P.p E ψ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff`.

-- Generated from ChapterPvmMeasure.lean — theorem BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff
import Mathlib
import Definitions.Def_ChapterPvmMeasure
open BookProof.ChapterPvmMeasure


open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (P : Pvm X H)
variable (P : Pvm X H) (ψ : H)

theorem BookProof.ChapterPvmMeasure.pvmMeasure_eq_zero_iff {E : Set X} (hE : MeasurableSet E) :
    pvmMeasure P ψ E = 0 ↔ P.p E ψ = 0 := by sorry
