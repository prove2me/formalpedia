-- Prove2me | Theorems.Thm_Erdos624_dense_pool_circuit_packing_small
-- name    : Erdos624.dense_pool_circuit_packing_small
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T09:16:33.287758+00:00
-- url     : https://prove2.me/theorems/77f1575d-abc7-40be-a936-12138fb79e7a
-- title:
--   Dense-pool circuit packing (small-m): $m^4\le 2^{120}a^{28}n^3$ (Erdős 624 Round 9)
-- statement:
--   Let $U$ be finite with $|U|=n\ge 1$, colour capacity $r=2$, and let $M$ be a set of $m$ colours each equipped with a pool $V_u\subseteq U$ satisfying $a|V_u|\ge n$ ($a\ge 1$) and a labelling $v_u:V_u\to\mathbb F_2^{k-1}$ such that every circuit of size at most eight in the pool is assigned colour $u$. If
--   $$
--   m\le 2^{30}a^{7},
--   $$
--   then
--   $$
--   m^4\le 2^{120}a^{28}n^3.
--   $$
--   This is the small-$m$ branch of Sol's dense-pool packing (Round 9). Constants loosened to $2^{120}$. It does **not** settle Erdős Problem 624 / PAIR / Step 17; the large-$m$ weight/Λ case is not included.
--
--   Formalization note: `Label` and `IsCircuit` are defined in the formal statement (same namespace) so the statement is self-contained.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); dense-pool circuit packing small-m branch derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean by Grok Bot for Ethan Cheung (Oct 24 2026). Honest: only the small-m branch (#M ≤ 2^{30} a^7); large-m weight/Λ case not included. Does NOT settle PAIR / #624.

import Mathlib
open Finset BigOperators

namespace Erdos624

/-- Label on a (k−1)-bit cube. -/
abbrev Label (k : ℕ) : Type := Fin (k - 1) → ZMod 2

/-- Minimal nonempty zero-sum set for a labelling. -/
def IsCircuit {V : Type*} [DecidableEq V] {k : ℕ} (v : V → Label k) (A : Finset V) : Prop :=
  A.Nonempty ∧ (∑ x ∈ A, v x) = 0 ∧
    ∀ ⦃S : Finset V⦄, S ⊆ A → S.Nonempty → S ≠ A → ∑ x ∈ S, v x ≠ 0

/-- Dense-pool circuit packing, small-m branch (Sol Round 9).
If `#M ≤ 2^{30} a^7` with dense pools and short-circuit compatibility,
then `m^4 ≤ 2^{120} a^{28} n^3`. Does not settle PAIR / #624. -/
theorem dense_pool_circuit_packing_small
    {U C : Type*} [Fintype U] [DecidableEq U] [DecidableEq C]
    {k : ℕ} (L : Finset U → Finset C) (hLcap : ∀ A, #(L A) ≤ 2)
    (M : Finset C) (pool : C → Finset U) (lab : C → U → Label k) (a : ℕ)
    (ha : 1 ≤ a)
    (hPool : ∀ u ∈ M, a * #(pool u) ≥ Fintype.card U)
    (hCompat : ∀ u ∈ M,
      ∀ A : Finset U, A ⊆ pool u → IsCircuit (lab u) A → #A ≤ 8 → u ∈ L A)
    (hn : 1 ≤ Fintype.card U)
    (hm : #M ≤ 2 ^ 30 * a ^ 7) :
    (#M) ^ 4 ≤ 2 ^ 120 * a ^ 28 * (Fintype.card U) ^ 3 := by sorry

end Erdos624
