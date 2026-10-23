-- Prove2me | Theorems.Thm_BookProof_ChapterG2_integral_haarAverage
-- name    : BookProof.ChapterG2.integral_haarAverage
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T16:59:56.682187+00:00
-- url     : https://prove2.me/theorems/4a692a5d-d02e-440b-a742-18c830dafffb
-- title:
--   `BookProof.ChapterG2.integral_haarAverage` [MeasurableSpace X] [MeasurableSMul G X] [MeasurableMul G] (μ : Measure X) [IsProbabilityMeasure μ] (hμ : ∀ g : G, MeasurePreserving (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG2`.
--
--   `BookProof.ChapterG2.integral_haarAverage` [MeasurableSpace X] [MeasurableSMul G X] [MeasurableMul G] (μ : Measure X) [IsProbabilityMeasure μ] (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ) (f : X → ℝ) (hint : Integrable (fun p : G × X => f (p.1⁻¹ • p.2)) (μG.prod μ)) : ∫ x, haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG2.integral_haarAverage`.

-- Generated from ChapterG2.lean — theorem BookProof.ChapterG2.integral_haarAverage
import Mathlib
import Definitions.Def_ChapterG2
import Definitions.Def_ChapterG
open BookProof.ChapterG2
open BookProof.ChapterG



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG2.integral_haarAverage [MeasurableSpace X] [MeasurableSMul G X]
    [MeasurableMul G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (f : X → ℝ)
    (hint : Integrable (fun p : G × X => f (p.1⁻¹ • p.2)) (μG.prod μ)) :
    ∫ x, haarAverage (μG := μG) f x ∂μ = ∫ x, f x ∂μ := by sorry
