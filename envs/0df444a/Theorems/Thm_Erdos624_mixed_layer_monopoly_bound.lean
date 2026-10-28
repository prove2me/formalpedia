-- Prove2me | Theorems.Thm_Erdos624_mixed_layer_monopoly_bound
-- name    : Erdos624.mixed_layer_monopoly_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:49.591749+00:00
-- url     : https://prove2.me/theorems/e72827bd-d1f9-40bd-9550-051c77457c40
-- title:
--   Central-layer monopoly forces mixed-layer colours (MIX), conditional on de Caen's bound (Erdős 624)
-- statement:
--   $C$ is a palette with $|C|=n=2^k$, $L$ assigns to each input $A$ a list $L(A)\subseteq C$ with $|L(A)|\le2$ (the empty input included; $b_0=|L(\varnothing)|$). Let $Z$ be a pool with $N=|Z|\ge k$, $1\le j\le k$, and let two distinct nonbottom colours $v_0,v_1\notin L(\varnothing)$ occupy the whole $j$-layer: $L(A)=\{v_0,v_1\}$ for every $A\in\binom Zj$ (MON). Assume the finite de Caen covering inequality on $Z$ (DC): for $1\le a\le k$, every family $\mathcal G\subseteq\binom Za$ meeting (from below) every $k$-subset of $Z$ satisfies $(N-k+1)\binom Na\le|\mathcal G|(N-a+1)\binom{k-1}{a-1}$. Let $M_Z$ be the number of colours $u\notin L(\varnothing)\cup\{v_0,v_1\}$ that are **irreducibly mixed**: for every size $1\le a\le k$ some $k$-face $Y\subseteq Z$ contains no $a$-input carrying $u$. **Theorem (MIX).** $$2(N-j+1)\binom{k-1}{j-1}\le(N-k+1)(M_Z+b_0+2)+2^{k-1}(k-1),$$ i.e. $M_Z\ge\frac{2(N-j+1)\binom{k-1}{j-1}-2^{k-1}(k-1)}{N-k+1}-b_0-2$.
--
--   Note: (DC) is de Caen's theorem (1983) and is taken as an explicit hypothesis; it is not proved here.
--
--   Source: 'Unrooted Coverage Forces Mixed-Layer Cores', (EXACT)/(CAP)/(LEVEL)/(SUM)/(MIX).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes 'Unrooted Coverage Forces Mixed-Layer Cores' and 'Polynomial Subpools and Cross-Pool Witness Accounting' (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem mixed_layer_monopoly_bound {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k j : ℕ) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : k ≤ #Z) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (v0 v1 : C) (hv : v0 ≠ v1) (hv0 : v0 ∉ L ∅) (hv1 : v1 ∉ L ∅)
    (hmon : ∀ A ⊆ Z, #A = j → L A = {v0, v1})
    (hDC : ∀ a, 1 ≤ a → a ≤ k → ∀ G : Finset (Finset U), (∀ A ∈ G, A ⊆ Z ∧ #A = a) →
      (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) →
      (#Z - k + 1) * (#Z).choose a ≤ #G * ((#Z - a + 1) * (k - 1).choose (a - 1))) :
    2 * ((#Z - j + 1) * (k - 1).choose (j - 1)) ≤
      (#Z - k + 1) * (#((univ : Finset C).filter (fun u : C => u ∉ L ∅ ∧ u ≠ v0 ∧ u ≠ v1 ∧
        ∀ a ∈ Icc (1 : ℕ) k, ∃ Y ∈ Z.powersetCard k, ∀ A ∈ Y.powersetCard a, u ∉ L A)) + #(L ∅) + 2) +
      2 ^ (k - 1) * (k - 1) := by sorry

end Erdos624
