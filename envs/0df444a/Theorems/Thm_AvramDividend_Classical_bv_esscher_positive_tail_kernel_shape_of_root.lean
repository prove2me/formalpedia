-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_shape_of_root
-- name    : AvramDividend.Classical.bv_esscher_positive_tail_kernel_shape_of_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:50:35.370784+00:00
-- url     : https://prove2.me/theorems/61873c37-24a7-40f2-aea1-1625a1e7ce12
-- title:
--   BV Esscher root supplies a continuous antitone causal L1 tail kernel
-- statement:
--   Construct the canonical positive-axis discounted jump-magnitude strict-tail kernel, extended by zero at nonpositive times, and prove continuity, antitonicity, nonnegativity and real L1 integrability. All analytical ingredients are already Proved, including the BV root discounted first moment, the weighted tail continuity theorem and the newly closed real-tail antitonicity and integrability theorems. This is the exact kernel-shape prerequisite for the Open bv_ac_esscher_scaled_subunit_kernel_scale_identification on the cstar finiteness route. Only the normalised subunit mass and scale-series identification remain.
-- source:
--   All imports are canonical Proved targets for the bounded-variation Esscher root and positive jump tails.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_antitone_of_finite_firstMoment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_magnitude_tail_continuous
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_integrable_of_root
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_positive_tail_kernel_shape_of_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
      {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume := by sorry
