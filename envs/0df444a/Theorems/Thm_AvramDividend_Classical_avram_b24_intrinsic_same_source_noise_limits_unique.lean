-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_intrinsic_same_source_noise_limits_unique
-- name    : AvramDividend.Classical.avram_b24_intrinsic_same_source_noise_limits_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:53:19.929192+00:00
-- url     : https://prove2.me/theorems/defe9df5-a7e7-4c10-aee5-c6e97acdc9cc
-- title:
--   Original intrinsic Gaussian and compensated marked residual source limits uniquely determine every stopped finite-mesh gain
-- statement:
--   Two pairs of source-noise witnesses formed as almost-sure limits on the same original Omega/P of the same intrinsic truncated Gaussian and small-mark compensated sources agree almost surely simultaneously for all deterministic times. Therefore arbitrary bounded stopped finite-step meshes using these source paths are almost surely equal, allowing proved same-source martingale centring to transfer without assuming an auxiliary Gaussian companion.
-- source:
--   Avram-Palmowski-Pistorius (2007) Proposition 4(i), (5.13) genuine ruin-stopped Ito-Meyer and finite-variation contact budget, combined with Protter stopped compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_intrinsic_same_source_noise_limits_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R R' J J' : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hR' : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R' u ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (J u ω)))
    (hJ' : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (J' u ω))) :
    (∀ᵐ ω ∂P, ∀ u, R u ω = R' u ω ∧ J u ω = J' u ω) ∧
    (∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
       (WG WJ : ℕ → Ω → ℝ) (σ : Ω → ℝ≥0),
      ∀ᵐ ω ∂P,
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)) =
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R' (b i) ω - R' (a i) ω)) ∧
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (J (b i) ω - J (a i) ω)) =
        (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (J' (b i) ω - J' (a i) ω))) := by sorry
