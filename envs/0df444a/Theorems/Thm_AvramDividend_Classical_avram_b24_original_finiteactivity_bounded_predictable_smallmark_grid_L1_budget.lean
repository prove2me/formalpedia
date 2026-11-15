-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_bounded_predictable_smallmark_grid_L1_budget
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_bounded_predictable_smallmark_grid_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:48:16.492202+00:00
-- url     : https://prove2.me/theorems/5e8d38fd-e427-4aeb-8f6b-a8cec1375a28
-- title:
--   Original finite-activity compensated smallmark bounded physical predictable mesh has explicit deterministic L1 first-moment budget
-- statement:
--   For the unchanged original finite-negative-activity Lévy source, any genuine intrinsic compensated smallmark process Jsmall and finite physical deterministic grid with ordered endpoints, uniformly bounded predictable coefficients W and integrable source increments and weighted gains, the full genuine marked noise grid gain is integrable and its expected absolute value is bounded by the sum of L times the exact original physical interval marked Poisson count expectation plus elapsed-time compensator drift bound. The result needs NO independence of the stopping mask and noise, no artificial compensated Poisson process, and no large-negative-jump moment. In the B24 stopped Itô-Meyer cash proof it supplies a quantitative L1 mesh budget once the original bounded predictable-mesh integrability from B218 and the true intrinsic Jsmall increments are available.
-- source:
--   Proved B24 true original Jsmall deterministic interval L1 rate, finite norm-sum and integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_bounded_predictable_smallmark_grid_L1_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hOrd : ∀ i ∈ S, a i ≤ b i)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hWBound : ∀ i ∈ S, ∀ ω, ‖W i ω‖ ≤ L)
    (hJM : ∀ i ∈ S, Integrable
      (fun ω => Jsmall (b i) ω - Jsmall (a i) ω) P)
    (hWI : ∀ i ∈ S, Integrable
      (fun ω => W i ω *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, W i ω * (Jsmall (b i) ω - Jsmall (a i) ω)) P ∧
    (∫ ω, ‖∑ i ∈ S,
      W i ω * (Jsmall (b i) ω - Jsmall (a i) ω)‖ ∂P) ≤
    ∑ i ∈ S, L *
      (((((b i - a i : ℝ≥0) : ℝ≥0∞) *
           X.ν (Ioo (-1 : ℝ) 0)).toReal) +
       ((b i : ℝ) - (a i : ℝ)) *
         ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖) := by sorry
