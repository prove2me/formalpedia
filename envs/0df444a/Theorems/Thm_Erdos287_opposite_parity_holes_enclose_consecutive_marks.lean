-- Prove2me | Theorems.Thm_Erdos287_opposite_parity_holes_enclose_consecutive_marks
-- name    : Erdos287.opposite_parity_holes_enclose_consecutive_marks
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:24:32.343016+00:00
-- url     : https://prove2.me/theorems/785b2572-b6bf-481d-8309-9973845b7bd9
-- title:
--   Opposite-parity omissions enclose consecutive marked positions
-- statement:
--   Let \(x<y\) be natural numbers of opposite parity, with \(x,y\notin D\). Suppose \(D\) contains at least one endpoint of every adjacent pair in \([x,y]\). Then some \(n,n+1\) strictly between \(x\) and \(y\) both belong to \(D\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Parity argument for transferring omitted multiples to unit gaps.

import Mathlib

theorem Erdos287.opposite_parity_holes_enclose_consecutive_marks (D : Finset ℕ) (x y : ℕ) (hxy : x < y)
    (hparity : x % 2 ≠ y % 2) (hx : x ∉ D) (hy : y ∉ D)
    (hcover : ∀ n, x ≤ n → n < y → n ∈ D ∨ n + 1 ∈ D) :
    ∃ n, x < n ∧ n + 1 < y ∧ n ∈ D ∧ n + 1 ∈ D := by sorry
