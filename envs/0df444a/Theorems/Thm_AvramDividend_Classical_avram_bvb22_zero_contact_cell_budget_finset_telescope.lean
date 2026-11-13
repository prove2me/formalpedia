-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_zero_contact_cell_budget_finset_telescope
-- name    : AvramDividend.Classical.avram_bvb22_zero_contact_cell_budget_finset_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:00:13.523232+00:00
-- url     : https://prove2.me/theorems/29cd195d-c2a0-4fcc-939d-4efa4f0ae449
-- title:
--   BV zero-reserve discounted cash and compensated negative-mark allowance telescopes across finite consecutive grid cells
-- statement:
--   Iterate the Proved source zero-reserve physical one-cell inequality over a monotone finite uniform grid. The discounted endpoint terms telescope and the total physical cash is bounded by the sum of one-sided negative-contact compensator allowances. This preserves the zero-contact term dropped by open interior masks in the BV finite-activity survival branch.
-- source:
--   Proved Avram source contact cell theorem 2453a94b and elementary finite-sum induction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_zero_contact_cell_budget_finset_telescope
    (q rate w0 : ℝ) (hq : 0 < q) (hrate : 0 ≤ rate)
    (hw0 : 0 ≤ w0) (u : ℕ → ℝ) (hu : Monotone u)
    (cash : ℕ → ℝ)
    (hCash : ∀ i : ℕ, cash i ≤ (q + rate) * w0 *
      ((Real.exp (-(q * u i)) - Real.exp (-(q * u (i + 1)))) / q))
    (n : ℕ) :
    (∑ i ∈ Finset.range n, cash i) +
      Real.exp (-(q * u n)) * w0 -
      Real.exp (-(q * u 0)) * w0 ≤
      ∑ i ∈ Finset.range n,
        rate * w0 * Real.exp (-(q * u i)) * (u (i + 1) - u i) := by sorry
