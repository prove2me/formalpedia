-- Prove2me | Theorems.Thm_Erdos287_nine_groups_with_two_scale_distances
-- name    : Erdos287.nine_groups_with_two_scale_distances
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:00:56.645156+00:00
-- url     : https://prove2.me/theorems/f9164f66-e262-5889-b2e3-3b084d3961a8
-- title:
--   Nine groups with two scales of pair distances
-- statement:
--   For positive group size $K$, let $1000Kle D$ and $64Dle E$. There are nine disjoint groups of $K$ integer positions from $0$ to $2E+2D+K$, labeled by two ternary digits. For positions in different groups with positive distance $d$, let $L=D$ if the high digits agree and $L=E$ otherwise. Then $(24/25)Lle dle(51/25)L$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Banks–Freiberg–Maynard, https://arxiv.org/abs/1404.5094. Polymath, https://arxiv.org/abs/1407.4897.

import Mathlib

theorem Erdos287.nine_groups_with_two_scale_distances (D E K : ℕ) (hK : 0 < K) (hD : 1000 * K ≤ D) (hE : 64 * D ≤ E) :
    ∃ z : (Fin 3 × Fin 3) × Fin K → ℕ, Function.Injective z ∧
      (∀ i, z i ≤ 2 * E + 2 * D + K) ∧
      ∀ i j : (Fin 3 × Fin 3) × Fin K, i.1 ≠ j.1 → z i < z j →
        let d := z j - z i
        let L := if i.1.2 = j.1.2 then D else E
        25 * d ≥ 24 * L ∧ 25 * d ≤ 51 * L := by sorry
