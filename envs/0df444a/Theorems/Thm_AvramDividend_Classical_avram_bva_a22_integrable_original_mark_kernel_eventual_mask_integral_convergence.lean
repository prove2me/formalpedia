-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
-- name    : AvramDividend.Classical.avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:32:30.330196+00:00
-- url     : https://prove2.me/theorems/73e5ae67-991b-4779-80de-edddc8eebe34
-- title:
--   Integrable original negative-mark kernel has convergent masked integral under a.e. eventual exhaustion without a spatial/physical rate
-- statement:
--   Let H be any integrable real source kernel on a measure space, such as the actual controlled negative-mark compensated jump integrand under the source predictable clock by Lévy product measure (whose integrability has already been Proved in original Wave7). For any measurable sequence of source spatial masks that eventually contains each mark-clock-path point almost everywhere, show that the integral of the masked kernel converges to the original unmasked integral along the prescribed same indices. Apply pinned Mathlib dominated convergence with dominator norm H, masked integrability, and a.e. eventual equality. This is the exact abstract L1 convergence transfer needed after source stopped compact kernel eventual unmask and original full predictable product integrability; no finite Lévy activity, global generator L1, or artificial fast spatial diagonal.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_integrable_original_mark_kernel_eventual_mask_integral_convergence
    {α : Type*} [m : MeasurableSpace α] (μ : Measure α)
    (H : α → ℝ) (hH : Integrable H μ)
    (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ p ∂μ, ∀ᶠ n : ℕ in atTop, p ∈ s n) :
    Tendsto (fun n : ℕ => ∫ p, if p ∈ s n then H p else 0 ∂μ)
      atTop (𝓝 (∫ p, H p ∂μ)) := by sorry
