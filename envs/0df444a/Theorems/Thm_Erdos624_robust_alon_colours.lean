-- Prove2me | Theorems.Thm_Erdos624_robust_alon_colours
-- name    : Erdos624.robust_alon_colours
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:48:43.906471+00:00
-- url     : https://prove2.me/theorems/06bfaf94-31fc-45f9-90ad-17fe0c56ea28
-- title:
--   Robust Alon inequality with a separate colour set: $32\sum_Y L_f(Y)\ge n\binom nk$ (Erdős 624)
-- statement:
--   Let $k\ge3$, $n=2^k$, let $U$ and $C$ be finite sets with $|U|=|C|=n$ and let $f:\mathcal P(U)\to C$ be arbitrary. Then$$32\sum_{Y\in\binom Uk}\bigl(n-|f[\mathcal P(Y)]|\bigr)\;\ge\; n\binom nk.$$This is the robust Alon inequality with input and colour sets separated (the previously verified `Erdos624.robust_alon_sum` is the case $C=U=\mathrm{Fin}\,2^k$). It is the special case $B=\emptyset$, $V=U$ of the conditioned pool inequality.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for every $|Y|\ge m$. This is an auxiliary finite inequality (the one-map 'robust Alon' loss bound and its ingredients) used in Sol's Round 10 analysis (parity-palette inequality, inequalities (11)/(13), top-layer-free resilience). It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: robust and conditioned Alon inequalities' (palette mechanism); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem robust_alon_colours {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (hC : Fintype.card C = 2 ^ k) (f : Finset U → C) :
    2 ^ k * #(powersetCard k (univ : Finset U)) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset U), (2 ^ k - #(Y.powerset.image f)) := by sorry

end Erdos624
