-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_finite_supported_geometric_renewal_uniform
-- name    : AvramDividend.Classical.positive_finite_supported_geometric_renewal_uniform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:18:31.249219+00:00
-- url     : https://prove2.me/theorems/2adbe761-d6c9-48c4-a567-8c8317c6b131
-- title:
--   A single finite positive geometric renewal measure has the cumulative Laplace identity for every positive parameter
-- statement:
--   Given an s-finite nonnegative-support measure κ whose total mass is strictly below a positive finite drift parameter δ, construct one measure β using the geometric sum of additive convolution powers of κ. Prove β has finite positive total mass, no mass on the negative half-line, finite cumulative values everywhere, and its cumulative positive Laplace transform equals (1/s) times the geometric reciprocal of the κ Laplace transform for every s>0. This fixed-measure theorem supports the root-shifted bounded-variation Esscher finite-Laplace package in the Avram Dividend Classical mission.
-- source:
--   Kuznetsov Kyprianou Rivero (2012) Theory of Scale Functions renewal treatment; Prove2Me accepted generic geometric renewal helpers and canonical BV-tilt proof cad1f045-cf66-47b7-aaa6-c4ec80ef1dc2.

import Theorems.Thm_AvramDividend_Classical_exists_sfinite_convolution_power_sequence
import Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
import Theorems.Thm_AvramDividend_Classical_finite_positive_geometric_measure_sum_of_mass_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_convolution_powers
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_geometric_measure_sum
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Measurability

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_finite_supported_geometric_renewal_uniform
    (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iio (0 : ℝ)) = 0)
    (δ : ℝ≥0∞) (hδ : 0 < δ) (hδfin : δ ≠ ⊤)
    (hgap : κ Set.univ < δ) :
    ∃ β : Measure ℝ,
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      β (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          (δ⁻¹ * (1 - δ⁻¹ *
            (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-s * z)) ∂κ))⁻¹)) := by sorry
