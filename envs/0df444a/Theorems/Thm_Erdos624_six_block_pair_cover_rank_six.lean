-- Prove2me | Theorems.Thm_Erdos624_six_block_pair_cover_rank_six
-- name    : Erdos624.six_block_pair_cover_rank_six
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:00.718242+00:00
-- url     : https://prove2.me/theorems/7dbc706d-d63f-4759-8b58-7775e0cb07d5
-- title:
--   Six-block half-measure pair cover with witness rank six (Erdős 624)
-- statement:
--   On $\{0,\dots,9\}$ let $A_0=\{0,3,4,7,9\}$, $A_1=\{0,3,5,6,8\}$, $A_2=\{0,1,2,4,8\}$, $A_3=\{2,4,5,6,7\}$, $A_4=\{1,6,7,8,9\}$, $A_5=\{1,2,3,5,9\}$. **Theorem.** (i) Each $|A_i|=5$. (ii) For all $x,y$ some $A_i$ avoids both, so the complements (each of measure exactly $1/2$) cover every pair, and every $8$-point face contains some $A_i$. (iii) The indicator vectors $\chi_{A_0},\dots,\chi_{A_5}$ are linearly independent over $\mathbb F_2$.
--
--   So an optimal six-block ($=2^{2+1}-2$) half-measure pair cover need not have witness span of dimension three. Source: 'Integral Near-Saturation on the Unchanged Assignment', ten-point example.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem six_block_pair_cover_rank_six : (∀ i : Fin 6, #((![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) = 5) ∧
    (∀ x y : Fin 10, ∃ i : Fin 6,
      x ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i ∧
      y ∉ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i) ∧
    (∀ c : Fin 6 → ZMod 2, (∀ x : Fin 10, ∑ i : Fin 6, c i *
      (if x ∈ (![{0,3,4,7,9},{0,3,5,6,8},{0,1,2,4,8},{2,4,5,6,7},{1,6,7,8,9},{1,2,3,5,9}] :
        Fin 6 → Finset (Fin 10)) i then 1 else 0) = 0) → c = 0) := by sorry

end Erdos624
