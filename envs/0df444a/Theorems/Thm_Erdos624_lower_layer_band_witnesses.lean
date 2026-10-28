-- Prove2me | Theorems.Thm_Erdos624_lower_layer_band_witnesses
-- name    : Erdos624.lower_layer_band_witnesses
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:01.337279+00:00
-- url     : https://prove2.me/theorems/c9c91cd6-797c-4ae5-aa26-7d04eba96b48
-- title:
--   Square-root gap and band witnesses (M)+(T)+(BAND) for capacity two, $k\ge1024$ (Erdős 624)
-- statement:
--   $L:\mathcal P(U)\to\mathcal P(C)$ is a list map with $|L(A)|\le 2$, $Z\subseteq U$ has $|Z|=k+1$, and every colour $u\in C$ is attained on every $k$-subface of $Z$: for every $x\in Z$ there is $A\subseteq Z\setminus\{x\}$ with $u\in L(A)$. Write $P_{<h}(Z)=\bigcup_{A\subseteq Z,|A|<h}L(A)$. Assume moreover $|C|=2^k=n$ and $k\ge1024$, and put $r=\lfloor\lfloor\sqrt k\rfloor/32\rfloor$, $h=\lfloor k/2\rfloor-r$, $R=\lfloor(k+1)/4\rfloor$. **Theorem.** (M) $|P_{<h}(Z)|>n/8$. (T) Fewer than $n/32$ colours are attained on inputs $A\subseteq Z$ with $|A|\le R$. (BAND) More than $3n/32$ colours are attained on some input $A\subseteq Z$ with $R<|A|<h$.
--
--   Non-vacuity: the hypotheses hold e.g. with capacity one, by identifying colours with subsets $B_c\subseteq Z\setminus\{z_0\}$ and putting $c\in L(B_c)$ and $c\in L(Z\setminus B_c)$.
--
--   Source: 'Unrooted Lower-Layer Forcing', (M), (T), (BAND). ($\lfloor\sqrt k\rfloor$ is `Nat.sqrt`, which agrees with the source's $\lfloor\sqrt k/32\rfloor$.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem lower_layer_band_witnesses {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1024 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (hZ : #Z = k + 1)
    (hcov : ∀ x ∈ Z, ∀ u : C, ∃ A ⊆ Z.erase x, u ∈ L A) :
    2 ^ k < 8 * #((Z.powerset.filter (fun A => #A < k / 2 - Nat.sqrt k / 32)).biUnion L) ∧
    32 * #((Z.powerset.filter (fun A => #A ≤ (k + 1) / 4)).biUnion L) < 2 ^ k ∧
    3 * 2 ^ k < 32 * #((Z.powerset.filter
      (fun A => (k + 1) / 4 < #A ∧ #A < k / 2 - Nat.sqrt k / 32)).biUnion L) := by sorry

end Erdos624
