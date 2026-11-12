-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb87_uniform_original_time_ledger_regroup
-- name    : AvramDividend.Classical.avram_gb87_uniform_original_time_ledger_regroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:18:46.960194+00:00
-- url     : https://prove2.me/theorems/bd427caf-c47b-4d62-a87e-53c2a7bd46b1
-- title:
--   Exact weighted original-time ledger regrouping on a product mesh
-- statement:
--   For any real-valued function x of nonnegative time and any drift c, the weighted sum of original-time increments x(t_i+Delta)-x(t_i)-Delta*c on a coarse uniform grid equals the weighted sum of the same-path centred increments on its uniform b-fold refinement. Each fine cell retains its coarse index floor(r/b). This is deterministic and follows the indexed finite-difference regrouping gb83 and the NNReal time bridge gb86.

import Mathlib
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb87_uniform_original_time_ledger_regroup
    (n m b : ℕ) (hb : 0 < b) (x : ℝ≥0 → ℝ) (c : ℝ) (g : ℕ → ℝ) :
    let D : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let d : ℝ≥0 := (n : ℝ≥0) / (((m + 1) * b : ℕ) : ℝ≥0)
    (Finset.range (m + 1)).sum (fun i =>
      g i * (x ((i : ℝ≥0) * D + D) - x ((i : ℝ≥0) * D) - (D : ℝ) * c)) =
    (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (x ((r : ℝ≥0) * d + d) - x ((r : ℝ≥0) * d) - (d : ℝ) * c)) := by sorry
