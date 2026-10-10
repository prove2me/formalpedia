-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_curryLI_indicator_prod
-- name    : BookProof.NsScalarVectorCurry.curryLI_indicator_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:04.183521+00:00
-- url     : https://prove2.me/theorems/1a861d00-538d-48fd-8504-1bdcf747f331
-- title:
--   `BookProof.NsScalarVectorCurry.curryLI_indicator_prod` {s : Set V} {t : Set W} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞) (hst : (μ.prod ν) (s ×ˢ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.curryLI_indicator_prod` {s : Set V} {t : Set W} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞) (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) : curryLI (fibMk (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ))) = indicatorConstLp 2 (hs.prod ht) hst (1 : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.curryLI_indicator_prod`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.curryLI_indicator_prod
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.curryLI_indicator_prod {s : Set V} {t : Set W} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞)
    (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) :
    curryLI (fibMk (indicatorConstLp 2 hs hμs (1 : ℂ)) (indicatorConstLp 2 ht hνt (1 : ℂ)))
      = indicatorConstLp 2 (hs.prod ht) hst (1 : ℂ) := by sorry
