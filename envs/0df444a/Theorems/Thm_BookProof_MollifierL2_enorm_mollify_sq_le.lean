-- Prove2me | Theorems.Thm_BookProof_MollifierL2_enorm_mollify_sq_le
-- name    : BookProof.MollifierL2.enorm_mollify_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T16:45:31.314979+00:00
-- url     : https://prove2.me/theorems/db7c2f60-9a7d-4092-ac03-3d003dc85ffe
-- title:
--   `BookProof.MollifierL2.enorm_mollify_sq_le` (u : E → ℂ) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) (hu :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMollifierL2`.
--
--   `BookProof.MollifierL2.enorm_mollify_sq_le` (u : E → ℂ) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ) (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) (hu : StronglyMeasurable u) (x : E) : ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ) ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.MollifierL2.enorm_mollify_sq_le`.

-- Generated from ChapterMollifierL2.lean — theorem BookProof.MollifierL2.enorm_mollify_sq_le
import Mathlib
import Definitions.Def_ChapterMollifierL2
open BookProof.MollifierL2



open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem BookProof.MollifierL2.enorm_mollify_sq_le (u : E → ℂ) (ρ : E → ℝ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρm : Measurable ρ)
    (hρ1 : ∫⁻ y, ENNReal.ofReal (ρ y) ∂μ = 1) (hu : StronglyMeasurable u) (x : E) :
    ‖∫ y, ρ y • (u (x - y) - u x) ∂μ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂μ := by sorry
