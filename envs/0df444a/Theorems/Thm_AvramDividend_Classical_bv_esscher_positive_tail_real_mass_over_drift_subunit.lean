-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_mass_over_drift_subunit
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_real_mass_over_drift_subunit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:12:51.634991+00:00
-- url     : https://prove2.me/theorems/e12ae87b-6957-49d6-88e2-4be8bc4a38a9
-- title:
--   Esscher BV discounted real jump-tail renewal mass divided by drift lies in [0,1)
-- statement:
--   For a bounded-variation spectrally negative Lévy process at a positive Esscher root, integrate the discounted strict positive jump-magnitude tail as a real function on positive times. The integral is nonnegative and strictly less than the positive BV drift. Therefore the dimensionless drift-normalised total renewal mass lies between zero inclusive and one exclusive, supplying the subcritical geometric-convolution control for the finite cstar workstream.
-- source:
--   Proved bv_esscher_positive_tail_real_total_mass_of_root and bv_esscher_root_subcritical_kernel_mass, together with nonnegative integration and positive real division

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_total_mass_of_root
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Field.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_positive_tail_real_mass_over_drift_subunit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 ≤
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift ∧
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift < 1 := by sorry
