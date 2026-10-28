-- Prove2me | Theorems.Thm_Erdos624_conditioned_alon_pool
-- name    : Erdos624.conditioned_alon_pool
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:48:42.296276+00:00
-- url     : https://prove2.me/theorems/240e4b9f-fbd3-4872-90bc-18d172bb072c
-- title:
--   Conditioned Alon inequality on an arbitrary pool $V$, $|V|\ge k+5$, general colour set (Erdős 624)
-- statement:
--   Let $k\ge2$, $n=2^k$, let $C$ be a finite set with $|C|=n$, let $U$ be a finite set (of any size) and $f:\mathcal P(U)\to C$ arbitrary. Let $B,V\subseteq U$ with $|B|\le k-2$ and $|V|\ge k+5$, and let $\mathcal K=\{Y\subseteq V: |Y|=k,\ B\subseteq Y\}$. Then$$32\sum_{Y\in\mathcal K}\bigl(n-|f[\mathcal P(Y)]|\bigr)\;\ge\; n\,|\mathcal K|.$$(If $B\not\subseteq V$ both sides vanish.) The colour set keeps size $n=2^k$ although the pool $V$ may be much smaller than $n$. This strengthens the previously verified `Erdos624.conditioned_alon` (which has colours $=$ inputs $=U$, $|U|=2^k$, pool $V=U$, $k\ge3$).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for every $|Y|\ge m$. This is an auxiliary finite inequality (the one-map 'robust Alon' loss bound and its ingredients) used in Sol's Round 10 analysis (parity-palette inequality, inequalities (11)/(13), top-layer-free resilience). It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: robust and conditioned Alon inequalities' (palette mechanism); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem conditioned_alon_pool {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 2 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (f : Finset U → C) (B V : Finset U) (hB : #B ≤ k - 2) (hV : k + 5 ≤ #V) :
    2 ^ k * #((powersetCard k V).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k V).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image f)) := by sorry

end Erdos624
