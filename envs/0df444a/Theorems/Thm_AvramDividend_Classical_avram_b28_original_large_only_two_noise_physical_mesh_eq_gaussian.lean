-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b28_original_large_only_two_noise_physical_mesh_eq_gaussian
-- name    : AvramDividend.Classical.avram_b28_original_large_only_two_noise_physical_mesh_eq_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:54:21.495666+00:00
-- url     : https://prove2.me/theorems/4f4cfeee-f0b8-4ab2-902b-06ccea8a8c20
-- title:
--   On large-only negative jump original Lévy paths, the exact ruin-clipped two-channel physical source mesh equals the Gaussian-source mesh
-- statement:
--   For the exact original B25 two-noise source, assume all actual negative sample-path jumps have size at most -1 (or zero) and the Lévy measure has no mass in (-1,0]. If R and B are simultaneously defined a.e. cutoff limits of the same intrinsic Gaussian residual and Jsmall is the original a.e. cutoff limit of the compensated small-band jump source, then every finite physical stopped predictable two-channel mesh sum G+J with the literal if sigma<=a_i then 0 stopping mask agrees almost surely with the Gaussian mesh sum formed using B. This combines uniqueness of intrinsic Gaussian source versions with the vanished original limiting compensated small-mark channel and retains physical time, signed compensation and ruin clipping.
-- source:
--   B25 original topcap/finitecap physical mesh formula; Prove2Me B28 accepted Gaussian source uniqueness d188880a and original small-band cutoff identity 489c24bc, 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators

theorem AvramDividend.Classical.avram_b28_original_large_only_two_noise_physical_mesh_eq_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hLarge : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (R B Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hBsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (σ : Ω → ℝ≥0) (S : Finset ℕ)
    (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) +
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
        (Jsmall (b i) ω - Jsmall (a i) ω)) =
      (∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
        (B (b i) ω - B (a i) ω)) := by sorry
