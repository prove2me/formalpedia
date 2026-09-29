-- Prove2me | Theorems.Thm_Erdos77_erdos_1947_pair_count_lt_factorial
-- name    : Erdos77.erdos_1947_pair_count_lt_factorial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T13:07:26.151072+00:00
-- url     : https://prove2.me/theorems/ef17fdb4-4c2f-4845-8f65-8ae0969a07ac
-- title:
--   A factorial dominates the pair count
-- statement:
--   For every integer k at least 6, the number of unordered pairs from a k-element set is strictly smaller than (k?2)!. This elementary factorial estimate supplies the numerical margin in the local-lemma bound.
-- source:
--   Auxiliary estimate for the floor local-lemma bound in Erdos, Some remarks on the theory of graphs (1947).

import Mathlib

namespace Erdos77
theorem erdos_1947_pair_count_lt_factorial (k : Nat) (hk : 6 <= k) :
    (Nat.choose k 2 : Real) < (Nat.factorial (k - 2) : Real) := by sorry
end Erdos77
