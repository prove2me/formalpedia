-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_enn_tendsto_zero_of_sq
-- name    : BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:17.404756+00:00
-- url     : https://prove2.me/theorems/321c7689-073e-44d1-aeba-0cc4201d001f
-- title:
--   `BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq` {u : ℕ → ℝ≥0∞} (h : Filter.Tendsto (fun k => u k ^ 2) Filter.atTop (nhds 0)) : Filter.Tendsto u Filter.atTop (nhds 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq` {u : ℕ → ℝ≥0∞} (h : Filter.Tendsto (fun k => u k ^ 2) Filter.atTop (nhds 0)) : Filter.Tendsto u Filter.atTop (nhds 0)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.enn_tendsto_zero_of_sq {u : ℕ → ℝ≥0∞}
    (h : Filter.Tendsto (fun k => u k ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by sorry
