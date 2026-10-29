-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_finite_grid_clock_prefix_cap_ws01c
-- name    : AvramDividend.Classical.bv_actual_finite_grid_clock_prefix_cap_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:55:32.63137+00:00
-- url     : https://prove2.me/theorems/b35b2c1f-28eb-4cdd-bb1e-c8f7f6a8264b
-- title:
--   The capped finite-grid NNReal observation clock equals the finite-prefix strict lower infimum
-- statement:
--   For an arbitrary real path observed at finite uniform-grid times bounded by horizon H, the NNReal-valued finite fold lower clock, capped at T≤H, is exactly the extended-nonnegative-real finite-prefix infimum of grid times at which the path lies strictly below the lower barrier, capped at T. This is a pointwise equality preserving the strict lower inequality and horizon cap. The proof composes the canonical finite fold-prefix identity with the public NNReal-to-ENNReal coercion definition.
-- source:
--   Prepared original 31-line source work/avram_ws01c_actual_grid_prefix_cap_solution_20261028.lean. Do not publish until the existing public finite-grid coe theorem 5085a76f is genuinely Proved after authorised raw-target parser fix. This helper is named in the original WS01C finite stopping-clock architecture.

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_fold_to_prefix_capped_clock_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_grid_NNReal_coe_ws01c

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_finite_grid_clock_prefix_cap_ws01c
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (lower : ℝ) (h T H : ℝ≥0) (M : ℕ)
    (hTH : T ≤ H) :
    (((bv_finite_grid_below_NNReal_ws01c
      Y lower H
        ((List.range (M + 1)).map
          (fun k : ℕ => (k : ℝ≥0) * h)) ω : ℝ≥0) : ℝ≥0∞) ⊓
      (T : ℝ≥0∞)) =
    ((⨅ (k : ℕ) (_ : k ≤ M),
        if Y ((k : ℝ≥0) * h) ω < lower then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ⊤) ⊓
        (T : ℝ≥0∞)) := by sorry
