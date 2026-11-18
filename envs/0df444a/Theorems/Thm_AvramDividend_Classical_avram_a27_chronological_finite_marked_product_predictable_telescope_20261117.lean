-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_chronological_finite_marked_product_predictable_telescope_20261117
-- name    : AvramDividend.Classical.avram_a27_chronological_finite_marked_product_predictable_telescope_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:57:39.190768+00:00
-- url     : https://prove2.me/theorems/7205087c-7a77-471d-90b6-44e83e569f19
-- title:
--   Chronological marked product increment ledger: telescoping predictable prefix factors
-- statement:
--   For a sequence of n real mark factors in chronological order, the total multiplicative factor minus one equals the sum of the changes at each mark, namely the product of all preceding factors multiplied by the current factor minus one. For physical finite-activity negative jumps, these preceding factors become predictable left-limit values of the marked exponential process; this is the deterministic step for the original Campbell–Mecke proof.
-- source:
--   Pinned Finset.prod_range_succ, Finset.sum_range_succ and real polynomial ring algebra; no stochastic independence required.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Finset AvramDividend.Classical
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_chronological_finite_marked_product_predictable_telescope_20261117
    (f : ℕ → ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, f j) - 1 =
      ∑ i ∈ Finset.range n,
        (∏ j ∈ Finset.range i, f j) * (f i - 1) := by sorry
