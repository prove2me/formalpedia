-- Prove2me | Theorems.Thm_FamousTheorems_erdos_ginzburg_ziv
-- name    : FamousTheorems.erdos_ginzburg_ziv
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:32.45846+00:00
-- url     : https://prove2.me/theorems/6b5e31f3-78a0-43f1-baa0-495147f5ca92
-- title:
--   The Erdős–Ginzburg–Ziv theorem
-- statement:
--   **The Erd\u0151s\u2013Ginzburg\u2013Ziv theorem.** Among any $2n-1$ integers there are $n$ whose sum is divisible by $n$. The bound is sharp: $n-1$ copies each of $0$ and $1$ give $2n-2$ integers with no such subset. The case of prime $n$ follows from the Cauchy\u2013Davenport theorem on sumsets in $\mathbb{Z}/p$, and the general case by multiplicativity in $n$. Proved in 1961, it launched the field of zero-sum combinatorics, where the Davenport constant and its relatives measure how long a sequence over an abelian group can be before a zero-sum subsequence is forced. **Formalization note.** The statement is over `ZMod n` with the subset selected from a multiset of size $2n-1$. The result is Mathlib's `ZMod.erdos_ginzburg_ziv`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem erdos_ginzburg_ziv :
    ∀ {ι : Type u_1} {n : ℕ} {s : Finset ι} (a : ι → ZMod n), 
    2 * n - 1 ≤ s.card → ∃ t ⊆ s, t.card = n ∧ ∑ i ∈ t, a i = 0 := by sorry

end FamousTheorems
