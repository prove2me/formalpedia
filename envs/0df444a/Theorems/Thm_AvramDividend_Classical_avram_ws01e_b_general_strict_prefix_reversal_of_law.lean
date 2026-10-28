-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_general_strict_prefix_reversal_of_law
-- name    : AvramDividend.Classical.avram_ws01e_b_general_strict_prefix_reversal_of_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:52:19.665527+00:00
-- url     : https://prove2.me/theorems/257dc2e0-5de2-4ab3-beab-d7acbe67e89e
-- title:
--   Strict terminal drawdown/minimum symmetry under reversal-invariant finite-vector laws and prefix covariance
-- statement:
--   Let μ be a reversal-invariant measure on real vectors indexed by Fin n, and let w(v,j) represent an observed time-j increment with the property that reversing the full vector reverses every prefix sum. Then for every strict threshold a the mass of the event that terminal-minus-earlier-prefix sum falls below a equals that of the event that an earlier-prefix sum falls below a. This includes arbitrary Esscher-weighted finite vector laws, assuming only their reversal symmetry and the explicit prefix covariance property. It is a strict version of the existing accepted non-strict finite-grid reversal, with the dependent-index extension function passed explicitly to avoid a problem-authoring scope bug.
-- source:
--   Accepted finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b and the established reversal argument used by finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_general_strict_prefix_reversal_of_law
    (n : ℕ) (μ : Measure (Fin n → ℝ)) (a : ℝ)
    (w : (Fin n → ℝ) → ℕ → ℝ)
    (hrev : Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ)
    (hprefix : ∀ (v : Fin n → ℝ) (k : ℕ), k ≤ n →
      Finset.sum (Finset.range k) (w (fun i => v i.rev)) =
      Finset.sum (Finset.range k) (fun j => w v (n - 1 - j))) :
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) < a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) < a} := by sorry
