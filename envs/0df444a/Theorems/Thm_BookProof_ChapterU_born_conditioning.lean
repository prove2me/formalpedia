-- Prove2me | Theorems.Thm_BookProof_ChapterU_born_conditioning
-- name    : BookProof.ChapterU.born_conditioning
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:28:46.470564+00:00
-- url     : https://prove2.me/theorems/d7aa418e-737b-4797-99c0-167b5d19e536
-- title:
--   `BookProof.ChapterU.born_conditioning` (Ψ : X → ℂ) (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : bornMeasure Ψ μ E ≠ 0) (_hfin : bornMeasure Ψ μ E ≠ ∞) : bornMeasure (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterU`.
--
--   `BookProof.ChapterU.born_conditioning` (Ψ : X → ℂ) (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : bornMeasure Ψ μ E ≠ 0) (_hfin : bornMeasure Ψ μ E ≠ ∞) : bornMeasure (conditionedState Ψ μ E) μ = (bornMeasure Ψ μ)[|E]
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterU.born_conditioning`.

-- Generated from ChapterU.lean — theorem BookProof.ChapterU.born_conditioning
import Mathlib
import Definitions.Def_ChapterU
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure
open BookProof.ChapterU


open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ChapterU.born_conditioning (Ψ : X → ℂ) (μ : Measure X) (E : Set X)
    (hE : MeasurableSet E) (hpos : bornMeasure Ψ μ E ≠ 0)
    (_hfin : bornMeasure Ψ μ E ≠ ∞) :
    bornMeasure (conditionedState Ψ μ E) μ = (bornMeasure Ψ μ)[|E] := by sorry
