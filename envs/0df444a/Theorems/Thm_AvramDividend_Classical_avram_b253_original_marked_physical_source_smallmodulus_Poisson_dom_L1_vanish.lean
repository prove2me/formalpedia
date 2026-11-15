-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
-- name    : AvramDividend.Classical.avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:39:13.134378+00:00
-- url     : https://prove2.me/theorems/3e3be685-1cf3-4ff5-a11a-2e6f83986e2b
-- title:
--   Original physical marked-cell Gaussian/negative-jump source small-modulus error vanishes in expected L1 under common finite-activity Poisson domination
-- statement:
--   For the actual finite-activity canonical marked physical-grid cells of the original spectrally negative source, suppose the number of marked cells at every mesh refinement is dominated almost surely by one common integrable original finite-horizon negative-jump count N, and each marked-cell source residual contribution has magnitude no greater than an explicit deterministic nonnegative modulus ε_m tending to zero. Then the signed sum of all true marked-cell errors is integrable for each mesh and its expected absolute magnitude converges to zero. The statement keeps the varying canonical marked sets and shared original Poisson count, so it is the correct L1-vanishing mechanism to combine original B247 marked-count domination with pathwise Gaussian/negative-mark Taylor residual modulus in the B236 ruin-clipped Itô source. The remaining stochastic cell Taylor modulus must be established separately.
-- source:
--   Finite norm triangle inequality, bounded weight per marked cell, and one common integrable original finite-activity Poisson count dominate every refinement. The expected absolute marked error is bounded by ε_m times the integrable Poisson mean; ε_m→0 gives L1 convergence via squeezing.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (marked : ℕ → Ω → Finset ℕ)
    (N : Ω → ℝ) (hNI : Integrable N P)
    (hNdom : ∀ m, ∀ᵐ ω ∂P,
      ((marked m ω).card : ℝ) ≤ N ω)
    (W : ℕ → Ω → ℕ → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P)
    (ε : ℕ → ℝ)
    (hεnonneg : ∀ m, 0 ≤ ε m)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hW : ∀ m, ∀ᵐ ω ∂P,
      ∀ i ∈ marked m ω, ‖W m ω i‖ ≤ ε m) :
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ marked m ω, W m ω i
    (∀ m, Integrable (F m) P) ∧
    Tendsto (fun m => ∫ ω, ‖F m ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
