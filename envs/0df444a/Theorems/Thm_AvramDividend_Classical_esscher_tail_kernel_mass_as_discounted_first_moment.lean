-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
-- name    : AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T16:13:36.141277+00:00
-- url     : https://prove2.me/theorems/e3f1c19a-6165-4b24-b0e9-32ee1a32b355
-- title:
--   Exact total mass of Esscher-discounted jump-tail kernel
-- statement:
--   For a positive jump-magnitude measure μ, Esscher-weight it by exp(-φz) and build its positive tail-density renewal kernel κφ. Its total mass is exactly ∫ z exp(-φz) μ(dz). Compose the generic layer-cake tail-density total-mass theorem with Mathlib's lintegral_withDensity_eq_lintegral_mul and ENNReal.ofReal_mul for the nonnegative jump coordinate. This enables direct application of the already Proved root subcriticality bound, giving κφ(ℝ)<δ, which is the key convergence criterion for the geometric renewal measure.
-- source:
--   Published positive_jump_tail_density_total_mass (upstream publication currently pending) and pinned MeasureTheory.lintegral_withDensity_eq_lintegral_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment
    (μ : Measure ℝ≥0) (φ : ℝ) :
    let μφ : Measure ℝ≥0 :=
      μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
    let κφ : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
    κφ Set.univ =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by sorry
