-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_causal_power_package
-- name    : AvramDividend.Classical.bv_esscher_canonical_causal_power_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:58:22.464249+00:00
-- url     : https://prove2.me/theorems/ad4c07cd-76c0-469e-ad58-1f6f08610ce0
-- title:
--   General standing BV Esscher causal convolution powers without absolute continuity
-- statement:
--   For every standing bounded-variation spectrally negative Lévy process at q>0, select the positive Esscher root and its exact drift-normalised positive jump-tail kernel. Construct continuous causal kernel and globally integrable nonnegative convolution powers with quadratic-geometric pointwise bounds. The assumptions do not require the Lévy measure to be absolutely continuous. This is a key analytic input to extending the known absolutely-continuous zero-barrier renewal representation to the general BV case.
-- source:
--   Proved bv_positive_esscher_root (3f64cde9), bv_esscher_root_positive_subunit_kernel_package (7d3344ce), causal_subunit_renewal_full_real_power_package (0aa46c71).

import Theorems.Thm_AvramDividend_Classical_bv_positive_esscher_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Continuous canonical Esscher convolution powers under standing BV assumptions alone. -/
theorem bv_esscher_canonical_causal_power_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ : ℝ) (κ : ℝ → ℝ) (ρ : ℝ) (F : ℕ → ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      Integrable κ volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) := by sorry

end AvramDividend.Classical
