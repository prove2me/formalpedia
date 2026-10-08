-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_gaugeAverage_isPhysicalObservable
-- name    : BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:53:56.503436+00:00
-- url     : https://prove2.me/theorems/3c427733-cb6f-4791-8eed-3b830fc7ea57
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable` (μ : Measure G) [μ.IsMulRightInvariant] (f : X → ℝ) : IsPhysicalObservable G (gaugeAverage (X := X) μ f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable` (μ : Measure G) [μ.IsMulRightInvariant] (f : X → ℝ) : IsPhysicalObservable G (gaugeAverage (X := X) μ f)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeCasimirAverage



open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]
variable {X : Type*}
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MulAction G X]

theorem BookProof.ChapterGaugeCasimirAverage.gaugeAverage_isPhysicalObservable (μ : Measure G) [μ.IsMulRightInvariant]
    (f : X → ℝ) : IsPhysicalObservable G (gaugeAverage (X := X) μ f) := by sorry
