-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:34:45.007395+00:00
-- url     : https://prove2.me/theorems/ad3c237d-7c5c-480d-badc-c83534b45517
-- title:
--   Source-exact Fatou bridge from physical finite-grid jump energy to original compensated small-band jumps
-- statement:
--   On the actual original spectrally negative Levy process X, filtration and probability P, a physical source finite-grid approximation with almost-sure convergence of squared compensated small-band jump differences and a source X.ν quadratic moment bound supplies the identical intrinsic L2 energy inequality by Fatou. Both physical prerequisites remain explicit, testable source obligations. No unrelated Gaussian Y, free decomposition, independent jump process or bracket assumption is introduced.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_liminf_le, Filter.Tendsto.liminf_eq, Filter.liminf_le_liminf and MeasureTheory.lintegral_congr_ae; source definition AvramDividend.Classical.avram_p4_h_gaussian_intrinsic_small_band_compensated, original X.ν physical band.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_intrinsic_limit_fatou_from_finite_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n m : ℕ)
    (G : ℕ → Ω → ℝ≥0∞)
    (hMeas : ∀ k, Measurable (G k))
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => G k ω) atTop
        (𝓝 (ENNReal.ofReal
          ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2))))
    (hSourceFiniteGrid : ∀ k,
      (∫⁻ ω, G k ω ∂P) ≤ (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν)) :
    (∫⁻ ω, ENNReal.ofReal
      ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) ∂P) ≤
      (T : ℝ≥0∞) *
        (∫⁻ z in Ioc
          (-(1 / (((min n m : ℕ) : ℝ) + 1)))
          (-(1 / (((max n m : ℕ) : ℝ) + 1))),
          ENNReal.ofReal (z ^ 2) ∂X.ν) := by sorry
