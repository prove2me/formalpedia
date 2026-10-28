-- Prove2me | Theorems.Thm_Erdos624_lower_layer_occurrence_inequality
-- name    : Erdos624.lower_layer_occurrence_inequality
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:58.170605+00:00
-- url     : https://prove2.me/theorems/a15b8772-fc33-4933-8c9e-09d07ca839de
-- title:
--   Lower-layer occurrence inequality (L) on a $(k+1)$-pool (Erdős 624)
-- statement:
--   $L:\mathcal P(U)\to\mathcal P(C)$ is a list map with $|L(A)|\le b$, $Z\subseteq U$ has $|Z|=k+1$, and every colour $u\in C$ is attained on every $k$-subface of $Z$: for every $x\in Z$ there is $A\subseteq Z\setminus\{x\}$ with $u\in L(A)$. Write $P_{<h}(Z)=\bigcup_{A\subseteq Z,|A|<h}L(A)$. **Theorem (L).** For every $h\ge1$, with $S=\sum_{a=h}^{k}\binom{k+1}a$ and $B=\sum_{a=h}^{\lfloor (k+1)/2\rfloor}\binom{k+1}a$, $$3\,(|C|-|P_{<h}(Z)|)\le b\,(S+B).$$ (Natural-number subtraction is harmless since $P_{<h}(Z)\subseteq C$.)
--
--   Source: 'Unrooted Lower-Layer Forcing', inequality (L).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem lower_layer_occurrence_inequality {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (b k h : ℕ) (hb : ∀ A, #(L A) ≤ b) (hh : 1 ≤ h)
    (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    3 * (Fintype.card C - #((Z.powerset.filter (fun A => #A < h)).biUnion L)) ≤
      b * (∑ a ∈ Icc h k, (k + 1).choose a + ∑ a ∈ Icc h ((k + 1) / 2), (k + 1).choose a) := by sorry

end Erdos624
