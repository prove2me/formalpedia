-- Prove2me | Theorems.Thm_BookProof_ChapterPvmMeasure_pvm_eq_zero_of_measure_zero
-- name    : BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:40.306313+00:00
-- url     : https://prove2.me/theorems/0cae02fb-abc4-464b-9f94-a3a988118aed
-- title:
--   `BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero` (hcyc : IsCyclic P ψ) {E : Set X} (hE : MeasurableSet E) (h0 : pvmMeasure P ψ E = 0) : P.p E = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPvmMeasure`.
--
--   `BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero` (hcyc : IsCyclic P ψ) {E : Set X} (hE : MeasurableSet E) (h0 : pvmMeasure P ψ E = 0) : P.p E = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero`.

-- Generated from ChapterPvmMeasure.lean — theorem BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero
import Mathlib
import Definitions.Def_ChapterPvmMeasure
open BookProof.ChapterPvmMeasure


open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (P : Pvm X H)
variable (P : Pvm X H) (ψ : H)

theorem BookProof.ChapterPvmMeasure.pvm_eq_zero_of_measure_zero (hcyc : IsCyclic P ψ) {E : Set X} (hE : MeasurableSet E)
    (h0 : pvmMeasure P ψ E = 0) : P.p E = 0 := by sorry
