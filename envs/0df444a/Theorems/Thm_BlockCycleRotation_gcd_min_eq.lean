-- Prove2me | Theorems.Thm_BlockCycleRotation_gcd_min_eq
-- name    : BlockCycleRotation.gcd_min_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T11:50:55.262431+00:00
-- url     : https://prove2.me/theorems/19363c08-6901-471a-8918-5c0652ea7f85
-- title:
--   $\gcd$ is unchanged by the reflection $k \mapsto \min(k, n-k)$
-- statement:
--   For $k \le n$,
--   $$\gcd(n, \min(k,\,n-k)) = \gcd(n,k).$$
--
--   The block cycle algorithm recurses on the shorter of the two segments, replacing a shift $k$ by $\min(k, n-k)$. This lemma says the greatest common divisor — which controls where the recursion terminates, by Lemma 11(1) — does not see that reflection, since $\gcd(n, n-k) = \gcd(n,k)$. It is what lets a bound proved for $2k \le n$ be transported to an arbitrary shift.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Average.lean#L31-L36

import Mathlib

open Finset

theorem BlockCycleRotation.gcd_min_eq {n k : ℕ} (h : k ≤ n) : Nat.gcd n (min k (n - k)) = Nat.gcd n k := by sorry
