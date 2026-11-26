-- Prove2me | Theorems.Thm_Erdos287_odd_positions_meet_quotas_outside_blocked_layers
-- name    : Erdos287.odd_positions_meet_quotas_outside_blocked_layers
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:33:17.010943+00:00
-- url     : https://prove2.me/theorems/38acf473-1673-4a62-a561-b3f1e81e1c52
-- title:
--   One-parity omission quotas outside heavily blocked layers
-- statement:
--   Let $H$ have no consecutive positions, and let $U$ be a set of odd candidate positions labeled by layers. Suppose each tested layer has at least $R+S$ candidates. Remove from $U$ the set $B$ of positions in or adjacent to $H$ and write $A=U\setminus B$. Then $H\cup A$ has no consecutive positions, and the number of layers with fewer than $R$ members in $A$, multiplied by $S$, is at most $|B|$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.odd_positions_meet_quotas_outside_blocked_layers (H U P : Finset ℕ) (label : ℕ → ℕ) (R S : ℕ)
    (hH : ∀ n ∈ H, n + 1 ∉ H) (hU : ∀ n ∈ U, Odd n)
    (hsize : ∀ p ∈ P, R + S ≤ (U.filter (fun n => label n = p)).card) :
    let B := U.filter (fun n => n ∈ H ∨ n - 1 ∈ H ∨ n + 1 ∈ H)
    let A := U \ B
    let X := H ∪ A
    (∀ n ∈ X, n + 1 ∉ X) ∧
      (P.filter (fun p => (A.filter (fun n => label n = p)).card < R)).card * S ≤ B.card := by sorry
