-- Prove2me | Theorems.Thm_Erdos287_supporting_multiple_outside_selected_run
-- name    : Erdos287.supporting_multiple_outside_selected_run
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T10:49:47.689947+00:00
-- url     : https://prove2.me/theorems/b5e32b0a-47a0-4381-8040-2c436e0e1381
-- title:
--   Supporting prime-power multiple outside a selected run
-- statement:
--   Let $D$ be the denominators of an exact unit reciprocal sum with no consecutive omissions. Suppose $n\in D$ lies in a block $[x,x+w)$, and $p^e\mid n$ with $p$ prime, $e\ge1$ and $p^e\ge w$. Then another selected multiple of $p^e$ lies outside that block.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.supporting_multiple_outside_selected_run (D : Finset ℕ) (m M x w n p e : ℕ) (hm : 0 < m)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ a ∈ D, (1 : ℚ) / a = 1)
    (hcover : ∀ a, m ≤ a → a + 1 ≤ M → a ∈ D ∨ a + 1 ∈ D)
    (hn : n ∈ D) (hin : n ∈ Finset.Ico x (x + w))
    (hp : p.Prime) (he : 1 ≤ e) (hsize : w ≤ p ^ e) (hq : p ^ e ∣ n) :
    ∃ y ∈ D, y ∉ Finset.Ico x (x + w) ∧ p ^ e ∣ y := by sorry
