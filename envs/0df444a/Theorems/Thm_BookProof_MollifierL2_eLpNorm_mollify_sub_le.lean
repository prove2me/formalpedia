-- Prove2me | Theorems.Thm_BookProof_MollifierL2_eLpNorm_mollify_sub_le
-- name    : BookProof.MollifierL2.eLpNorm_mollify_sub_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:45:47.41498+00:00
-- url     : https://prove2.me/theorems/7e672305-1e03-43e5-84d0-b06518b04edb
-- title:
--   `BookProof.MollifierL2.eLpNorm_mollify_sub_le` (u : E → ℂ) (hu : StronglyMeasurable u) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMollifierL2`.
--
--   `BookProof.MollifierL2.eLpNorm_mollify_sub_le` (u : E → ℂ) (hu : StronglyMeasurable u) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) {C : ℝ≥0∞} (hC : ∀ y : E, ρ y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) 2 μ ≤ C) : eLpNorm (fun x => ∫ y, ρ y • (u (x - y) - u x) ∂μ) 2 μ ≤ C
--
--   Formalization note: Lean 4 identifier `BookProof.MollifierL2.eLpNorm_mollify_sub_le`.

-- Generated from ChapterMollifierL2.lean — theorem BookProof.MollifierL2.eLpNorm_mollify_sub_le
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2



open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BookProof.MollifierL2.eLpNorm_mollify_sub_le (u : E → ℂ) (hu : StronglyMeasurable u) (ρ : E → ℝ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1)
    {C : ℝ≥0∞} (hC : ∀ y : E, ρ y ≠ 0 → eLpNorm (fun x => u (x - y) - u x) 2 μ ≤ C) :
    eLpNorm (fun x => ∫ y, ρ y • (u (x - y) - u x) ∂μ) 2 μ ≤ C := by sorry
