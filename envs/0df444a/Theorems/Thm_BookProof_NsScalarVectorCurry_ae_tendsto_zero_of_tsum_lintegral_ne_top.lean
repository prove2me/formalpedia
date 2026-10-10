-- Prove2me | Theorems.Thm_BookProof_NsScalarVectorCurry_ae_tendsto_zero_of_tsum_lintegral_ne_top
-- name    : BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:12:25.455964+00:00
-- url     : https://prove2.me/theorems/f3c9a4a2-ad94-4e20-b351-8f2122468d79
-- title:
--   `BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top` {X : Type*} [MeasurableSpace X] {ρ : Measure X} (ψ : ℕ → X → ℝ≥0∞) (hmeas : ∀ k, AEMeasurable (ψ k) ρ) (h :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNsScalarVectorCurry`.
--
--   `BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top` {X : Type*} [MeasurableSpace X] {ρ : Measure X} (ψ : ℕ → X → ℝ≥0∞) (hmeas : ∀ k, AEMeasurable (ψ k) ρ) (h : ∑' k, ∫⁻ x, ψ k x ∂ρ ≠ ∞) : ∀ᵐ x ∂ρ, Filter.Tendsto (fun k => ψ k x) Filter.atTop (nhds 0)
--
--   Formalization note: Lean 4 identifier `BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top`.

-- Generated from ChapterNsScalarVectorCurry.lean — theorem BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top
import Mathlib
import Definitions.Def_ChapterNsScalarVectorCurry
open BookProof.NsScalarVectorCurry


open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate


noncomputable section

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W}

variable [SigmaFinite μ] [SigmaFinite ν]

theorem BookProof.NsScalarVectorCurry.ae_tendsto_zero_of_tsum_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    (ψ : ℕ → X → ℝ≥0∞) (hmeas : ∀ k, AEMeasurable (ψ k) ρ)
    (h : ∑' k, ∫⁻ x, ψ k x ∂ρ ≠ ∞) :
    ∀ᵐ x ∂ρ, Filter.Tendsto (fun k => ψ k x) Filter.atTop (nhds 0) := by sorry
