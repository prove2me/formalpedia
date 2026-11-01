-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_predictable_marked_campbell_integrable
-- name    : AvramDividend.Classical.avram_wave4_p1_sigma_finite_predictable_marked_campbell_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:40:55.758816+00:00
-- url     : https://prove2.me/theorems/855fd687-40fa-4fdc-942b-7bc02ea07937
-- title:
--   Nonnegative and signed L1 predictable marked Campbell transfer from adapted count rectangles
-- statement:
--   Let two measures M and N on predictable time-history and marks agree on all elementary adapted count-compensation rectangles (initial-time and strict-future adapted sets paired with measurable mark sets). Assume a countable increasing measurable mark-band exhaustion and finite M-mass on each band, without requiring globally finite mass. Then every measurable nonnegative predictable marked kernel G has identical extended integrals against M and N; every real predictable marked kernel F integrable under M is also integrable under N, and its two signed Bochner integrals agree. The proof invokes the canonically Proved countable-band predictable marked-measure uniqueness theorem to establish M=N, then transports both integral types. It does not assume arbitrary Campbell integral identities, and it applies to the actual Lévy N_X only after 04-A constructs its expected marked measure and proves the adapted rectangle intensity law. The stochastic centred integral mean-zero then requires interpreting M as expectation of N_X and N as ds⊗P⊗ν.
-- source:
--   Canonically Proved avram_wave4_p1_sigma_finite_marked_predictable_measure_unique UUID 85791e69-1071-4a55-a3a3-c402870c4066; Applebaum, Levy Processes and Stochastic Calculus, predictable marked Poisson integration.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique

open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_sigma_finite_predictable_marked_campbell_integrable
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ι × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ι)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ι) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (G : ((ι × Ω) × E) → ℝ≥0∞)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] G)
    (F : ((ι × Ω) × E) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] F)
    (hFi : Integrable F M) :
    (∫⁻ p, G p ∂M) = (∫⁻ p, G p ∂N) ∧
      (Integrable F N ∧ (∫ p, F p ∂M) = ∫ p, F p ∂N) := by sorry
