-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_discounted_first_moment_of_nonzero_no_zero_atom
-- name    : AvramDividend.Classical.positive_discounted_first_moment_of_nonzero_no_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:00:35.271834+00:00
-- url     : https://prove2.me/theorems/ce8a473f-4dce-4e88-a9e0-5f7d0b56b045
-- title:
--   Strict positive Esscher discounted first jump moment from nontrivial atom-free magnitude measure
-- statement:
--   Given a nonzero jump magnitude measure with zero atom at the origin, its Esscher-weighted first moment is strictly positive. Absolute continuity of withDensity transfers the zero-atom condition, esscher_exponential_withDensity_nonzero_of_nonzero transfers nontriviality because the exponential weight is strictly positive, and canonical Proved positive_first_moment_of_nonzero_without_zero_atom finishes. This strictly positive discounted first moment supplies the missing ρ>0 exact normalised mass required by causal_subunit_renewal_full_real_power_package in the BV branch of cstar finiteness.
-- source:
--   Canonical Proved esscher_exponential_withDensity_nonzero_of_nonzero and positive_first_moment_of_nonzero_without_zero_atom; Mathlib withDensity_absolutelyContinuous.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_first_moment_of_nonzero_without_zero_atom
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_discounted_first_moment_of_nonzero_no_zero_atom
    (μ : Measure ℝ≥0) (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0)
    (φ : ℝ)
    (hf : AEMeasurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) μ) :
    0 < ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂
      (μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))) := by sorry
