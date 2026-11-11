-- Prove2me | solution 1 for levy_foundations_charFun_zero_double_half_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:20:49.811949+00:00
-- url     : https://prove2.me/submissions/80113a80-9ad0-4d9b-8599-d56363d31557

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_levy_foundations_covarianceMatrix
import Theorems.Thm_levy_foundations_posDefCharFun
import Theorems.Thm_levy_foundations_covarianceMatrixPosSemidef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Matrix Complex
open scoped ComplexOrder

/-- The three-point characteristic covariance matrix forces the
half-frequency bound when the doubled-frequency coefficient vanishes. -/
theorem solution
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (ξ : ℝ)
    (hzero : charFun ν (2 * ξ) = 0) :
    ‖charFun ν ξ‖ ^ 2 ≤ (1 / 2 : ℝ) := by
  let p : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  let a : ℂ := charFun ν ξ
  let t : Fin 3 → ℝ := ![0, ξ, 2 * ξ]
  have hpos : LevyFoundations.isPositiveDefinite
      (fun η : ℝ => charFun ν η) := by
    simpa [p] using levy_foundations_posDefCharFun p
  have hpsd :
      (LevyFoundations.covarianceMatrix
        (fun η : ℝ => charFun ν η) t).PosSemidef :=
    levy_foundations_covarianceMatrixPosSemidef _ t hpos
  have hzero_neg : charFun ν (-(2 * ξ)) = 0 := by
    rw [charFun_neg, hzero]
    simp
  have h0 : charFun ν 0 = 1 := by
    simp [charFun_zero, Measure.real, measure_univ]
  have hleft : ξ + -(2 * ξ) = -ξ := by ring
  have hright : 2 * ξ + -ξ = ξ := by ring
  have hmatrix :
      LevyFoundations.covarianceMatrix
        (fun η : ℝ => charFun ν η) t =
        !![(1 : ℂ), star a, 0;
           a, 1, star a;
           0, a, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LevyFoundations.covarianceMatrix, t, a,
        h0, hzero, hzero_neg, charFun_neg, sub_eq_add_neg,
        hleft, hright]
  have hdet := hpsd.det_nonneg
  rw [hmatrix] at hdet
  have hdet' : (0 : ℂ) ≤ 1 - 2 * star a * a := by
    convert hdet using 1 <;>
      simp [Matrix.det_fin_three] <;> ring
  have hreal : 0 ≤ (1 - 2 * star a * a).re :=
    (Complex.nonneg_iff.mp hdet').1
  have hs : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq a).symm
  have hnorm : 0 ≤ 1 - 2 * ‖a‖ ^ 2 := by
    convert hreal using 1
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq] <;>
      nlinarith [hs]
  dsimp [a] at hnorm
  linarith
