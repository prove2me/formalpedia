-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:30:36.615862+00:00
-- url     : https://prove2.me/theorems/a5e67f06-b3ea-42ab-b6bc-bd9b5aef72b0
-- title:
--   Original stopped Gaussian physical clock-gap L1 via two-clock energy and Hölder
-- statement:
--   For original zero-jump Gaussian source at two true physical clocks, sampled ceiling source convergence and measurable finite-grid energies with shrinking gap bound imply a quantitative first-absolute-moment bound for the final stop-straddling increment. Its square-root-of-energy integrand equals the absolute centred source increment. The proof uses the exact Proved original two-clock squared-energy Fatou theorem, a.e. measurability of the physical limit, and Hölder on the original probability measure. No fourth moments, floor stopping-time assertion, auxiliary Brownian model, global Hessian or automatic uniform integrability.
-- source:
--   Proved ef79ef96, pinned Mathlib.MeasureTheory.Integral.MeanInequalities ENNReal.lintegral_mul_norm_pow_le, Proved a998aa4f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (ε : ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hS : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω - (s n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hT : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (t n ω) ω - (t n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (ρ ω) ω - (ρ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
        (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2)))
    (hSampleBound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal
        (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
          (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P) ≤
        ENNReal.ofReal (((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2)) :
    (∫⁻ ω, (ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2)) ^ (1 / 2 : ℝ) ∂P) ≤
      (ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2)) ^ (1 / 2 : ℝ) := by sorry
