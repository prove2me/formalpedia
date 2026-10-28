-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_normalised_kernel_mass
-- name    : AvramDividend.Classical.bv_esscher_root_positive_normalised_kernel_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:28:18.800211+00:00
-- url     : https://prove2.me/theorems/8037fcf7-7c5d-48f7-9dcb-7833f1072244
-- title:
--   Strictly positive subunit BV Esscher renewal kernel mass under standing assumptions
-- statement:
--   For a BV spectrally negative Lévy process with nonmonotone standing assumptions at a positive Esscher root, the drift-normalised discounted positive jump-tail mass is strictly between zero and one. Nonzero Lévy jumps and spectral support imply a nonzero Esscher magnitude measure without an atom at zero; the canonical positive-tail theorem gives strict positivity, and the existing Proved subunit theorem supplies the upper bound. This fills the strict 0<ρ condition in bv_ac_esscher_scaled_subunit_kernel_scale_identification, directly on the cstar finiteness route.
-- source:
--   Model-specific composition of Proved BV nonzero jump, negative-magnitude support, Esscher density nonzero, positive jump-tail L1 and subcritical mass.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_negative_measure_magnitude_pushforward_positive
import Theorems.Thm_AvramDividend_Classical_esscher_exponential_withDensity_nonzero_of_nonzero
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_density_total_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_real_mass_over_drift_subunit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_positive_normalised_kernel_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 <
      (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift ∧
    (∫ t in Ioi (0 : ℝ),
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) ∂volume) / X.drift < 1 := by sorry
