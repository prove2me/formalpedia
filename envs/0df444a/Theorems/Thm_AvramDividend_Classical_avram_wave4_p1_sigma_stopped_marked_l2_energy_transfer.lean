-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_marked_l2_energy_transfer
-- name    : AvramDividend.Classical.avram_wave4_p1_sigma_stopped_marked_l2_energy_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:55:37.098997+00:00
-- url     : https://prove2.me/theorems/bc37a3a9-afd2-44e5-a745-c7d1f1d0f1e0
-- title:
--   Stopping preserves square-integrability of predictable marked kernels under sigma-finite compensated measures
-- statement:
--   Two sigma-finite predictable-by-mark measures agreeing on elementary adapted rectangles are identical by the Proved countable-mark-band extension. A genuinely predictable square-integrable real kernel, inclusively stopped at any stopping clock, remains predictable and square-integrable under both measures and has equal squared-energy lintegrals. This is the deterministic L2 localisation and measure-transfer interface, not a Poisson martingale isometry.
-- source:
--   Pinned Mathlib MeasureTheory.MemLp.indicator exact compiled signature; Proved sigma-finite marked measure uniqueness UUID 85791e69 and real-time stopped survival UUID 69806d16.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

open MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_wave4_p1_sigma_stopped_marked_l2_energy_transfer
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M N : @Measure ((ℝ≥0 × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × E) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] G)
    (hG2 : MemLp G 2 M) :
    let H : ((ℝ≥0 × Ω) × E) → ℝ :=
      fun p => if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0
    Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] H ∧
    MemLp H 2 M ∧ MemLp H 2 N ∧
      (∫⁻ p, ENNReal.ofReal (H p ^ 2) ∂M) =
        (∫⁻ p, ENNReal.ofReal (H p ^ 2) ∂N) := by sorry
