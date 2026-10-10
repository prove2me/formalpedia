-- Prove2me | Theorems.Thm_BookProof_MollifierL2_eLpNorm_translate
-- name    : BookProof.MollifierL2.eLpNorm_translate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:45:07.450679+00:00
-- url     : https://prove2.me/theorems/c73ad30b-8885-402c-a8f6-e25168ab70c5
-- title:
--   `BookProof.MollifierL2.eLpNorm_translate` {p : ℝ≥0∞} {f : E → F} (hf : AEStronglyMeasurable f μ) (a : E) : eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMollifierL2`.
--
--   `BookProof.MollifierL2.eLpNorm_translate` {p : ℝ≥0∞} {f : E → F} (hf : AEStronglyMeasurable f μ) (a : E) : eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ
--
--   Formalization note: Lean 4 identifier `BookProof.MollifierL2.eLpNorm_translate`.

-- Generated from ChapterMollifierL2.lean — theorem BookProof.MollifierL2.eLpNorm_translate
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2



open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BookProof.MollifierL2.eLpNorm_translate {p : ℝ≥0∞} {f : E → F} (hf : AEStronglyMeasurable f μ) (a : E) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ := by sorry
