-- Prove2me | Theorems.Thm_Erdos287_exceptional_endpoint_carries
-- name    : Erdos287.exceptional_endpoint_carries
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:06:37.396912+00:00
-- url     : https://prove2.me/theorems/0cca8ef2-953c-43d2-945c-90286d1265fb
-- title:
--   Next-layer congruences for the exceptional dense endpoint forms
-- statement:
--   Suppose the least and greatest denominators in a finite unit-fraction representation of one are $m,M$, with $0<m$ and $M<3m$. For $j\ge1$, if $M=6\cdot3^j$, then $4\cdot3^j$ is selected and $5\cdot3^j$ is omitted. If $M=15\cdot5^j$, let $T$ consist of the omitted cofactors $c$ in $\{6,7,8,9,11,12,13,14\}$ at $5^j$. Then $\sum_{c\in T}72072/c\equiv2\pmod5$. If $T$ is a singleton, its only element is 6 or 11.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.exceptional_endpoint_carries (D : Finset ℕ) (m M j : ℕ) (hm : 0 < m) (hj : 1 ≤ j)
    (hD : D ⊆ Finset.Icc m M) (hmD : m ∈ D) (hMD : M ∈ D)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1) (hratio : M < 3 * m) :
    (M = 6 * 3 ^ j → 4 * 3 ^ j ∈ D ∧ 5 * 3 ^ j ∉ D) ∧
    (M = 15 * 5 ^ j →
      let T := (Finset.Icc 6 14).filter (fun c => c ≠ 10 ∧ c * 5 ^ j ∉ D)
      (∑ c ∈ T, 72072 / c) % 5 = 2 ∧ (∀ c, T = {c} → c = 6 ∨ c = 11)) := by sorry
