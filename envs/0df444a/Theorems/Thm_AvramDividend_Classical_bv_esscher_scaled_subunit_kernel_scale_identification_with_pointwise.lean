-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
-- name    : AvramDividend.Classical.bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:33:11.442995+00:00
-- url     : https://prove2.me/theorems/72f2341a-9e14-4cef-a6ae-f6fc7663097e
-- title:
--   Exact BV Esscher renewal scale primitive with its canonical pointwise kernel
-- statement:
--   For a standing spectrally negative bounded-variation Lévy process, represent the tilted positive q-scale function by the drift-normalised continuous Esscher renewal density. The returned kernel retains its explicit strict-tail pointwise formula under infinite-activity and atomic Lévy jump measures, enabling direct application of the canonical origin-divergence theorem.
-- source:
--   Strengthening of remote-accepted source bv_ac_esscher_scaled_subunit_kernel_scale_identification SHA-256 5b16757f500faa9eb9349f58f3cc0a531b9d7b0e8c46124fdefeb8b9448ced8d, eliminating the unused absolute-continuity binder and preserving the exact canonical kernel identity from the independently proved pointwise kernel-match strengthening.

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match_with_pointwise
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_geometric_scale_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_subunit_any_real_recursion_power_bounds
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_density_continuous_integrable_for_any_recursion
import Theorems.Thm_AvramDividend_Classical_causal_full_convolution_powers_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_causal_subunit_shifted_renewal_series_summable
import Theorems.Thm_AvramDividend_Classical_causal_subunit_full_convolution_pointwise_integrable
import Theorems.Thm_AvramDividend_Classical_real_convolution_power_recursion_measurable
import Theorems.Thm_AvramDividend_Classical_causal_continuous_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_from_scaled_kernel_real_density
import Theorems.Thm_AvramDividend_Classical_geometric_atom_plus_real_density_full_cumulative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < b ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (∀ F : ℕ → ℝ → ℝ,
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        (∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x,
              (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y))) := by sorry
