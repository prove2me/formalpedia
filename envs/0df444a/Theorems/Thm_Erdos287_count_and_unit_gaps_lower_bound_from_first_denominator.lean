-- Prove2me | Theorems.Thm_Erdos287_count_and_unit_gaps_lower_bound_from_first_denominator
-- name    : Erdos287.count_and_unit_gaps_lower_bound_from_first_denominator
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:52:21.009967+00:00
-- url     : https://prove2.me/theorems/58febd55-0217-4ffc-be47-9b2f0f3139e5
-- title:
--   Lower bounds on denominator count and unit gaps from the first denominator
-- statement:
--   Let \(m=n_0<\cdots<n_{k-1}=M\) be positive integers with \(m>1\) and \(\sum_i1/n_i=1\). Then \(k\ge(e-1)(m-1)\). If every gap is at most two, the number \(t_1\) of unit gaps satisfies \(t_1\ge(2e-1)m-M-2e\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Integral comparison and counting unit gaps.

import Mathlib

theorem Erdos287.count_and_unit_gaps_lower_bound_from_first_denominator (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ) (hmin : 1 < f 0)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    (Real.exp 1 - 1) * ((f 0 : ℝ) - 1) ≤ (k : ℝ) ∧
    ((∀ i, i + 1 < k → f (i + 1) - f i ≤ 2) →
      (2 * Real.exp 1 - 1) * f 0 - f (k - 1) - 2 * Real.exp 1 ≤
        (((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card : ℝ)) := by sorry
