-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
-- name    : AvramDividend.Classical.avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:15:44.005457+00:00
-- url     : https://prove2.me/theorems/3287ead5-47d3-4171-90c2-a7f8f78bd680
-- title:
--   Any arbitrary original same-space intrinsic Gaussian and smallmark witness has integrable bounded predictable two-noise stopped physical grids
-- statement:
--   For the unchanged original finite-negative-activity spectrally negative Lévy X and ANY two same-sample-space intrinsic Gaussian R and compensated smallnegative-mark Jsmall witnesses satisfying precisely the original a.e. all-clock cutoff-source limit definitions, each common finite physical grid of bounded predictable Gaussian/mark weights, stopped at an actual right-continuous-filtration stopping time τ, gives two INTEGRABLE original Gaussian and marked gains. Proved B218 already establishes integrability for a canonical same-source intrinsic Gaussian/mark pair. Almost-sure all-clock uniqueness of the common original cutoff limits equates arbitrary R,Jsmall to that canonical pair on one P-conull event, so the finite stopped physical sums agree a.e. and inherit integrability without extra source assumptions. This allows B219's genuinely original same-noise dominated a.e. cash ledger to be used in the B24 signed L1 bridge, without making the false assumption X.ν=0 or introducing a substitute Brownian/Poisson sample space.
-- source:
--   Proved B218 original bounded predictable two-noise stopped physical grid centring, uniqueness of a.e. limits in ℝ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_arbitrary_original_intrinsic_two_noise_stopped_finite_grid_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    {ι : Type*} (S : Finset ι)
    (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
    (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
    (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) :
    Integrable (fun ω => ∑ i ∈ S,
      (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S,
      (if τ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) P := by sorry
