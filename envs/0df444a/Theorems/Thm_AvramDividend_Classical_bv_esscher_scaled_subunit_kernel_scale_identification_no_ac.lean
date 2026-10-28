-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_no_ac
-- name    : AvramDividend.Classical.bv_esscher_scaled_subunit_kernel_scale_identification_no_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:19:15.435545+00:00
-- url     : https://prove2.me/theorems/a55056c9-3651-4c81-b909-10f76c31bd98
-- title:
--   Canonical BV Esscher scaled renewal primitive from standing assumptions without absolute continuity
-- statement:
--   Under the standing spectrally negative Lévy assumptions and bounded variation, identify the exponentially tilted q-scale function as the drift-normalised primitive of the exact continuous causal Esscher renewal series. This removes the jump-measure absolute-continuity hypothesis from the previously proved scaled-subunit kernel identification theorem. Its accepted Lean proof is structurally unchanged apart from removing that unused hypothesis.
-- source:
--   Source-derived strengthening of already Proved bv_ac_esscher_scaled_subunit_kernel_scale_identification (1ca4a724-85b7-48bf-bae4-37890ef7055b), accepted remote source SHA-256 5b16757f500faa9eb9349f58f3cc0a531b9d7b0e8c46124fdefeb8b9448ced8d. The source's only occurrence of the hac hypothesis was its binder.

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_scaled_tail_real_kernel_match
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

theorem AvramDividend.Classical.bv_esscher_scaled_subunit_kernel_scale_identification_no_ac
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ),
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
