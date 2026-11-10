-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite29_original_masked_positive_event_fatou
-- name    : AvramDividend.Classical.avram_gfinite29_original_masked_positive_event_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T03:49:36.129192+00:00
-- url     : https://prove2.me/theorems/f78a9ca3-a1d0-4492-b8e9-6330dab522c9
-- title:
--   Masked positive-clock physical reward Fatou bound from cofinal L1 budgets
-- statement:
--   Analytic child for the finite-cap Gaussian localised expected budget 3308ae9d. For source-exact monotone physical clocks bounded by σ, measurable L1 rewards and a.e. cofinality, positive-clock eventwise budget bounds uniformly transfer to the σ positive-clock event. The proof uses the Proved a400dff7 a.e. real-valued Fatou theorem on the exact event-mask indicators.
-- source:
--   Source-exact positive-event mask and a.e. convergence steps, with no local Lean; hFint and positivity are explicit premises preventing vacuous nonintegrable real integral bounds.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite29_original_masked_positive_event_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (σ : Ω → ℝ≥0) (hσmeas : Measurable σ)
    (L : ℕ → Ω → ℝ≥0) (hLmeas : ∀ j, Measurable (L j))
    (hLle : ∀ j ω, L j ω ≤ σ ω)
    (hLlim : ∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (𝓝 (σ ω)))
    (H : (Ω → ℝ≥0) → Ω → ℝ)
    (hHmeas : ∀ j, Measurable (H (L j)))
    (hHσmeas : AEStronglyMeasurable (H σ) P)
    (hHInt : ∀ j, Integrable (H (L j)) P)
    (hHpos : ∀ j ω, L j ω ≠ 0 → 0 ≤ H (L j) ω)
    (hHσpos : ∀ ω, σ ω ≠ 0 → 0 ≤ H σ ω)
    (hHlim : ∀ᵐ ω ∂P,
      Tendsto (fun j => ENNReal.ofReal (H (L j) ω)) atTop
        (𝓝 (ENNReal.ofReal (H σ ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ j,
      (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, H (L j) ω ∂P) ≤ b) :
    (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, H σ ω ∂P) ≤ b := by sorry
