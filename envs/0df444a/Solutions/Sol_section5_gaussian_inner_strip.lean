-- Prove2me | solution 1 for section5_gaussian_inner_strip
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:22:15.053003+00:00
-- url     : https://prove2.me/submissions/83d0d354-1922-4c29-a4c8-43a8172d1fa5

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example









theorem section5_gaussian_interval_bound (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Set.Icc (-t) t) ≤ 2*t/(Real.sqrt (2*Real.pi)) := by
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    have hh : Real.exp (-x^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    simpa using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (Real.sqrt (2*Real.pi))⁻¹)
  have hi : IntegrableOn (gaussianPDFReal 0 1) (Set.Icc (-t) t) :=
    (integrable_gaussianPDFReal 0 1).integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (Real.sqrt (2*Real.pi))⁻¹) (Set.Icc (-t) t) :=
    continuous_const.integrableOn_Icc
  change ((gaussianReal 0 1) (Set.Icc (-t) t)).toReal ≤ _
  rw [gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ x))]
  calc
    _ ≤ ∫ _ in Set.Icc (-t) t, (Real.sqrt (2*Real.pi))⁻¹ := integral_mono hi hc hpdf
    _ = _ := by
      simp only [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]
      rw [max_eq_left (by linarith : 0 ≤ t- -t)]
      ring













end
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real {x | |inner ℝ w x| ≤ t} ≤
      2*t/Real.sqrt (2*Real.pi) := by
  let L := innerSL ℝ w
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin n))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    simp [L, innerSL_apply_norm, hw]
  have hevent : {x : EuclideanSpace ℝ (Fin n) | |inner ℝ w x| ≤ t} = L ⁻¹' Set.Icc (-t) t := by
    ext x
    simp [L, abs_le]
  change ((stdGaussian (EuclideanSpace ℝ (Fin n))) {x | |inner ℝ w x| ≤ t}).toReal ≤ _
  rw [hevent, ← Measure.map_apply L.continuous.measurable measurableSet_Icc, hmap]
  exact section5_gaussian_interval_bound t ht
