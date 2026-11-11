-- Prove2me | solution 1 for levy_foundations_public_prob_topup_normalises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:28:02.084936+00:00
-- url     : https://prove2.me/submissions/f70db850-56b1-4cbc-bf56-60106ed8adf1

import Mathlib.Probability.Independence.CharacteristicFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

/-- Scaling a finite measure and adding its mass deficit as a Dirac atom
produces a probability measure. -/
theorem solution (ν : Measure ℝ) (Mass : ℝ) (hMass_pos : 0 < Mass)
    (hν_mass : ν Set.univ ≤ ENNReal.ofReal Mass) :
    IsProbabilityMeasure
      ((ENNReal.ofReal Mass⁻¹) • ν +
        (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν Set.univ)) •
          Measure.dirac (0 : ℝ)) := by
  refine ⟨?_⟩
  have hM_inv_nn : (0 : ℝ) ≤ Mass⁻¹ := le_of_lt (inv_pos.mpr hMass_pos)
  have h_sum_eq : ν Set.univ + (ENNReal.ofReal Mass - ν Set.univ) =
      ENNReal.ofReal Mass :=
    add_tsub_cancel_of_le hν_mass
  calc
    (((ENNReal.ofReal Mass⁻¹) • ν +
      (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν Set.univ)) •
        Measure.dirac (0 : ℝ)) : Measure ℝ) Set.univ
        = ENNReal.ofReal Mass⁻¹ * ν Set.univ +
          (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν Set.univ)) *
            Measure.dirac (0 : ℝ) Set.univ := by
          simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal Mass⁻¹ * ν Set.univ +
          (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν Set.univ)) * 1 := by
          rw [show Measure.dirac (0 : ℝ) Set.univ = 1 from by
            rw [Measure.dirac_apply' _ MeasurableSet.univ]
            simp]
    _ = ENNReal.ofReal Mass⁻¹ *
          (ν Set.univ + (ENNReal.ofReal Mass - ν Set.univ)) := by
          rw [mul_one]
          ring
    _ = ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal Mass := by rw [h_sum_eq]
    _ = ENNReal.ofReal ((Mass : ℝ)⁻¹ * (Mass : ℝ)) :=
          (ENNReal.ofReal_mul hM_inv_nn).symm
    _ = ENNReal.ofReal 1 := by rw [inv_mul_cancel₀ hMass_pos.ne']
    _ = 1 := ENNReal.ofReal_one
