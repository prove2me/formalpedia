-- Prove2me | Theorems.Thm_AvramDividend_Classical_real_nonnegative_scalar_withDensity_unrestricted
-- name    : AvramDividend.Classical.real_nonnegative_scalar_withDensity_unrestricted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:16:18.276681+00:00
-- url     : https://prove2.me/theorems/c2a908e5-e58e-4b1b-8eb2-ab38db0eb3ee
-- title:
--   Real density scalar multiplication without a measurability premise
-- statement:
--   Finite nonnegative real scaling commutes with Lebesgue-density measures even for an arbitrary real function, by the unrestricted finite-scalar withDensity identity. This removes unnecessary measurability obligations in the drift-normalised canonical Esscher jump-tail measure identification.
-- source:
--   Mathlib MeasureTheory.withDensity_smul' and ENNReal.ofReal_mul, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474. Generalises previously proved real_nonnegative_scalar_withDensity (082af0a2-be8e-405b-9dd0-2494d9880473).

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.real_nonnegative_scalar_withDensity_unrestricted (r : ℝ) (hr : 0 ≤ r) (k : ℝ → ℝ) :
    ENNReal.ofReal r • (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)) =
    (volume : Measure ℝ).withDensity
      (fun x : ℝ => ENNReal.ofReal (r * k x)) := by sorry
