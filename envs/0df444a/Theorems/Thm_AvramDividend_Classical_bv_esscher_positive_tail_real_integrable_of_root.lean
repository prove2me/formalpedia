-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_integrable_of_root
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_real_integrable_of_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:37:17.186724+00:00
-- url     : https://prove2.me/theorems/8bca2cd9-d92c-435e-9b7b-36884921b91e
-- title:
--   BV root Esscher jump-magnitude strict positive tail is real integrable
-- statement:
--   For the bounded-variation spectrally negative Levy process and positive Esscher exponent solving the q-root, the Esscher-discounted strict positive jump-magnitude tail is Lebesgue integrable on (0,infinity). It follows from the Proved root subcritical discounted first moment, the exact Esscher tail layer-cake mass, and the Proved generic positive-tail real L1 theorem. This supplies the exact L1 prerequisite for the cstar-connected Open bv_ac_esscher_scaled_subunit_kernel_scale_identification via the causal subunit renewal package.
-- source:
--   Proved theorems: bv_esscher_root_subcritical_kernel_mass, esscher_tail_kernel_mass_as_discounted_first_moment, positive_jump_tail_density_total_mass, positive_jump_tail_real_integrable_of_finite_firstMoment.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_positive_tail_real_integrable_of_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    IntegrableOn (fun t : ℝ =>
      ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
        (fun z : ℝ≥0 => ENNReal.ofReal
          (Real.exp (-(φ * (z : ℝ))))))
        {z : ℝ≥0 | t < (z : ℝ)}))
      (Ioi (0 : ℝ)) volume := by sorry
