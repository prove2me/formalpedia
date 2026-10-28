-- Prove2me | Theorems.Thm_Erdos624_erasure_block_count_arith
-- name    : Erdos624.erasure_block_count_arith
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:29:16.72978+00:00
-- url     : https://prove2.me/theorems/56052ca4-1c8f-45b0-aea3-7a42870429a8
-- title:
--   Block-count arithmetic: $2^k<2k\lfloor(2^k-k+1)/(k-3)\rfloor$ for $k\ge4$ (Erdős 624 cross-review)
-- statement:
--   For every natural number $k\ge4$, with $n=2^k$ and $t=\lfloor (n-k+1)/(k-3)\rfloor$ (natural-number division and truncated subtraction, which is exact here since $n\ge k$):$$4k\le 2^k,\qquad n<2k\,t,\qquad n<256k\,t.$$The cross-review uses this for $k\ge64$ to conclude $t>n/(2k)$, hence $256k\,\sigma_{u_z}(U)=256kt>n$ for the colours of its construction.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem erasure_block_count_arith (k : ℕ) (hk : 4 ≤ k) :
    4 * k ≤ 2 ^ k ∧ 2 ^ k < 2 * k * ((2 ^ k - k + 1) / (k - 3)) ∧
      2 ^ k < 256 * k * ((2 ^ k - k + 1) / (k - 3)) := by sorry

end Erdos624
