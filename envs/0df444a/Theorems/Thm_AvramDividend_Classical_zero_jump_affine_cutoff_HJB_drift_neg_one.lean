-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_HJB_drift_neg_one
-- name    : AvramDividend.Classical.zero_jump_affine_cutoff_HJB_drift_neg_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:34:08.60867+00:00
-- url     : https://prove2.me/theorems/dd8ed71f-032f-42cd-a1ae-022d81a5b7fc
-- title:
--   Cutoff affine Gaussian candidate satisfies canonical HJB generator and gradient inequalities at positive reserves
-- statement:
--   When the Lévy jump measure is zero and the canonical drift coefficient is −1, the piecewise affine candidate w(z)=0 for z<0 and w(z)=z−1 otherwise satisfies Γw(y)−w(y)=−y≤0 and w′(y)=1 for every y>0. The generator integrability condition also holds. This verifies all HJB conditions of the Gaussian counterexample for discount q=1.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), HJB generator and derivative conditions.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_affine_cutoff_deriv_eq_one_positive
import Theorems.Thm_AvramDividend_Classical_zero_jump_affine_cutoff_generator_eq_drift

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.zero_jump_affine_cutoff_HJB_drift_neg_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hc : X.c = -1)
    (y : ℝ) (hy : 0 < y) :
    X.GeneratorIntegrable (fun z : ℝ => if z < 0 then 0 else z - 1) y ∧
      X.generator (fun z : ℝ => if z < 0 then 0 else z - 1) y - (fun z : ℝ => if z < 0 then 0 else z - 1) y ≤ 0 ∧
      1 ≤ deriv (fun z : ℝ => if z < 0 then 0 else z - 1) y := by sorry
