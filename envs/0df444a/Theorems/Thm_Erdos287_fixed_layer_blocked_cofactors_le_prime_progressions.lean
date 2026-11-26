-- Prove2me | Theorems.Thm_Erdos287_fixed_layer_blocked_cofactors_le_prime_progressions
-- name    : Erdos287.fixed_layer_blocked_cofactors_le_prime_progressions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:21:22.855659+00:00
-- url     : https://prove2.me/theorems/ce7b50ed-9167-497a-89f4-b2057b047454
-- title:
--   Bound on blocked cofactors of one layer by progression counts
-- statement:
--   Fix $p>0$, a finite set $A$ of cofactors in $[L,B]$, a finite set $C$ of positive cofactors, and a finite set $Q$ of neighboring labels. Call $a\in A$ blocked if $ap=bq+\epsilon$ for some $b\in C$, $q\in Q$, and $\epsilon\in\{-1,1\}$. The number of blocked cofactors is at most the sum over $b,\epsilon$ of the number of $q\in Q$ with $Lp\le bq+1$, $q\le\lfloor (Bp+1)/b\rfloor$ and $p\mid bq+\epsilon$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.fixed_layer_blocked_cofactors_le_prime_progressions (A C Q : Finset ℕ) (p L B : ℕ) (hp : 0 < p)
    (hA : ∀ a ∈ A, L ≤ a ∧ a ≤ B) (hC : ∀ b ∈ C, 0 < b) :
    let choices := C ×ˢ ({-1, 1} : Finset ℤ)
    let blocked := A.filter (fun a : ℕ => ∃ i ∈ choices, ∃ q ∈ Q,
      (a : ℤ) * p = (i.1 : ℤ) * q + i.2)
    let progression := fun i : ℕ × ℤ => Q.filter (fun q =>
      L * p ≤ i.1 * q + 1 ∧ q ≤ (B * p + 1) / i.1 ∧ (p : ℤ) ∣ (i.1 : ℤ) * q + i.2)
    blocked.card ≤ ∑ i ∈ choices, (progression i).card := by sorry
