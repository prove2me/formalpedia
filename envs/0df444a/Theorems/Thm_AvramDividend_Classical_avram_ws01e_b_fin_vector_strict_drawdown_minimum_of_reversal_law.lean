-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
-- name    : AvramDividend.Classical.avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:49:47.012155+00:00
-- url     : https://prove2.me/theorems/186f7ecf-8c52-43ce-8519-e8f14d677f4f
-- title:
--   Strict finite-grid drawdown/minimum symmetry for any reversal-invariant vector law
-- statement:
--   For any measure μ on real-valued vectors indexed by Fin n whose law is invariant under reversal of the coordinates, the strict event that the terminal sum minus an earlier prefix sum is below threshold a has exactly the same μ-mass as the strict event that an earlier prefix sum is below a. This is a purely finite-dimensional strict-event reversal theorem, valid for arbitrary finite measures including Esscher-weighted vector laws; it does not use stochastic-process or exponential-clock assumptions.
-- source:
--   Adapts the Proved nonstrict finite-vector identity finite_grid_drawdown_minimum_probability_of_reversal_law_ws01e_b (7b5b78d7), applying the same exact range equality and measurable reversal equivalence with strict threshold comparisons.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

theorem AvramDividend.Classical.avram_ws01e_b_fin_vector_strict_drawdown_minimum_of_reversal_law
    (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) (a : ℝ)
    (hrev : MeasureTheory.Measure.map
      (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) μ = μ) :
    let w : (Fin n → ℝ) → ℕ → ℝ :=
      fun v j => if hj : j < n then v ⟨j, hj⟩ else 0
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range n) (w v) -
        Finset.sum (Finset.range k.val) (w v) < a} =
    μ {v : Fin n → ℝ | ∃ k : Fin n.succ,
      Finset.sum (Finset.range k.val) (w v) < a} := by sorry
