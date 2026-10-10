-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_curryLI_setIntegral_rect
-- name    : BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:11.886979+00:00
-- url     : https://prove2.me/theorems/cc6637b2-7ba1-4d49-920b-979150f8f322
-- title:
--   `BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect` (f : Lp (Lp ℂ 2 ν) 2 μ) {s : Set V} {t : Set W} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect` (f : Lp (Lp ℂ 2 ν) 2 μ) {s : Set V} {t : Set W} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞) (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) : ∫ z in s ×ˢ t, (curryLI f : V × W → ℂ) z ∂(μ.prod ν) = ∫ x in s, (∫ y in t, ((f : V → Lp ℂ 2 ν) x : W → ℂ) y ∂ν) ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.curryLI_setIntegral_rect (f : Lp (Lp ℂ 2 ν) 2 μ) {s : Set V} {t : Set W}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hνt : ν t ≠ ∞)
    (hst : (μ.prod ν) (s ×ˢ t) ≠ ∞) :
    ∫ z in s ×ˢ t, (curryLI f : V × W → ℂ) z ∂(μ.prod ν)
      = ∫ x in s, (∫ y in t, ((f : V → Lp ℂ 2 ν) x : W → ℂ) y ∂ν) ∂μ := by sorry
