-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_lintegral_eLpNorm_slice_sq
-- name    : BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:38.393445+00:00
-- url     : https://prove2.me/theorems/b23ec926-7642-428c-8d48-dbc5a354cd23
-- title:
--   `BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq` (F : V × W → ℂ) (hF : AEStronglyMeasurable F (μ.prod ν)) : ∫⁻ x, (eLpNorm (fun y => F (x, y)) 2 ν) ^ 2 ∂μ = (eLpNorm F 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq` (F : V × W → ℂ) (hF : AEStronglyMeasurable F (μ.prod ν)) : ∫⁻ x, (eLpNorm (fun y => F (x, y)) 2 ν) ^ 2 ∂μ = (eLpNorm F 2 (μ.prod ν)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.lintegral_eLpNorm_slice_sq (F : V × W → ℂ) (hF : AEStronglyMeasurable F (μ.prod ν)) :
    ∫⁻ x, (eLpNorm (fun y => F (x, y)) 2 ν) ^ 2 ∂μ = (eLpNorm F 2 (μ.prod ν)) ^ 2 := by sorry
