-- Prove2me | Theorems.Thm_Erdos287_endpoint_extremal_cover_split_divisor_mass
-- name    : Erdos287.endpoint_extremal_cover_split_divisor_mass
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-27T00:23:08.237026+00:00
-- url     : https://prove2.me/theorems/56c95983-6878-4116-8c70-f6bd59c134c1
-- title:
--   Divisor-indexed splits force distinct selected denominators
-- statement:
--   For an endpoint-extremal exact pair cover, take any collection of divisors $d<m$ of $m^2$ with $m+m^2/d\le M$. Each split of $1/m$ into the reciprocals at $m+d$ and $m+m^2/d$ requires one output already selected. The outputs from different splits are disjoint, giving the stated lower bounds on selection count and reciprocal mass.
-- source:
--   Erdős Problem 287. Exact reciprocal covers with extremal endpoints.

import Mathlib

theorem Erdos287.endpoint_extremal_cover_split_divisor_mass (D B : Finset ℕ) (m M : ℕ) (hm : 1 < m) (hmD : m ∈ D)
    (hD : D ⊆ Finset.Icc m M)
    (hcover : ∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hextreme : ∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m))
    (hB : ∀ d ∈ B, 0 < d ∧ d < m ∧ d ∣ m * m ∧ m + m * m / d ≤ M) :
    let S := D.filter (fun n => ∃ d ∈ B, n = m + d ∨ n = m + m * m / d)
    B.card ≤ S.card ∧
      (∑ d ∈ B, (1 : ℚ) / ((m + m * m / d : ℕ) : ℚ)) ≤ ∑ n ∈ S, (1 : ℚ) / n := by sorry
