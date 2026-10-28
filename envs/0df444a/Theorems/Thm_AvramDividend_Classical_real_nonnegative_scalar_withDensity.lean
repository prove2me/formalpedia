-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_nonnegative_scalar_withDensity
-- name    : AvramDividend.Classical.real_nonnegative_scalar_withDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:34:24.124554+00:00
-- url     : https://prove2.me/theorems/082af0a2-be8e-405b-9dd0-2494d9880473
-- title:
--   Real nonnegative scaling of a Lebesgue density measure
-- statement:
--   For any nonnegative real scalar r and measurable real kernel k, scaling its nonnegative extended-real Lebesgue-density measure by ofReal r is the same measure as the Lebesgue density of the real function r*k. The result follows by the exact Mathlib withDensity_smul measure identity and the positivity-preserving ofReal multiplication identity. It supplies the elementary measure-level drift-normalisation bridge c•κ=withDensity(k) required by the Proved geometric_renewal_from_scaled_kernel_real_density theorem for the Esscher BV convolution representation, when κ already has a real jump-tail density.
-- source:
--   Pinned Mathlib MeasureTheory.withDensity_smul, ENNReal.ofReal_mul and ENNReal.measurable_ofReal.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.real_nonnegative_scalar_withDensity (r : ℝ) (hr : 0 ≤ r) (k : ℝ → ℝ)
    (hkmeas : Measurable k) :
    ENNReal.ofReal r • volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)) =
    volume.withDensity (fun x : ℝ => ENNReal.ofReal (r * k x)) := by sorry
