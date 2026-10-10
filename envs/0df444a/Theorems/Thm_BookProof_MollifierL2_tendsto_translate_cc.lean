-- Prove2me | Theorems.Thm_BookProof_MollifierL2_tendsto_translate_cc
-- name    : BookProof.MollifierL2.tendsto_translate_cc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:46:43.78576+00:00
-- url     : https://prove2.me/theorems/e59edf30-6760-4adf-b821-30cbd76f31e4
-- title:
--   `BookProof.MollifierL2.tendsto_translate_cc` {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {g : E → F} (hg : Continuous g) (hcs : HasCompactSupport g) : Tendsto (fun a : E => eLpNorm (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMollifierL2`.
--
--   `BookProof.MollifierL2.tendsto_translate_cc` {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {g : E → F} (hg : Continuous g) (hcs : HasCompactSupport g) : Tendsto (fun a : E => eLpNorm (fun x => g (x - a) - g x) p μ) (𝓝 0) (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.MollifierL2.tendsto_translate_cc`.

-- Generated from ChapterMollifierL2.lean — theorem BookProof.MollifierL2.tendsto_translate_cc
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2



open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BookProof.MollifierL2.tendsto_translate_cc {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {g : E → F}
    (hg : Continuous g) (hcs : HasCompactSupport g) :
    Tendsto (fun a : E => eLpNorm (fun x => g (x - a) - g x) p μ) (𝓝 0) (𝓝 0) := by sorry
