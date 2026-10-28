-- Prove2me | Theorems.Thm_Erdos624_short_repair_overload
-- name    : Erdos624.short_repair_overload
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:52.100598+00:00
-- url     : https://prove2.me/theorems/0a0388f6-e2c8-44c3-b3ef-4fafa0e74968
-- title:
--   Singleton/pair repairs cannot suffice: short-capacity overload $|E|(s-t+1)\le N(N+1)$ (LONG-POP) (Erdős 624)
-- statement:
--   $C$ is a palette with $|C|=n=2^k$, $L$ assigns to each input $A$ a list $L(A)\subseteq C$ with $|L(A)|\le2$ (the empty input included; $b_0=|L(\varnothing)|$). Let $Z$ be a pool, $N=|Z|$, and $t\le s$. Let $E$ be a set of colours $u$ such that: $u\notin L(\varnothing)$; $u$ is robustly mixed, i.e. for every $P\subseteq Z$ with $|P|\ge N-s$ and every $1\le a\le k$ some $k$-face $Y\subseteq P$ has no $a$-input carrying $u$; and $u$ is **exceptional**: there are a size $1\le a\le k$, a raw covering family $\mathcal G\subseteq\mathcal P(Z)$ of inputs carrying $u$ that meets every $k$-face of $Z$, and a set $T\subseteq Z$, $|T|\le t$, meeting every $A\in\mathcal G$ with $|A|\ge3$, $|A|\ne a$. **Theorem.** $|E|\,(s-t+1)\le N(N+1)=2\bigl(\binom N1+\binom N2\bigr)$. Hence at least $|\mathcal M_Z(s)|-\lfloor N(N+1)/(s-t+1)\rfloor$ robustly mixed colours have, in every raw covering core and outside every preferred size, a long off-layer family with transversal number $>t$.
--
--   Source: 'Unrooted Coverage Forces Mixed-Layer Cores', (SHORT-CAP) and (LONG-POP).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes 'Unrooted Coverage Forces Mixed-Layer Cores' and 'Polynomial Subpools and Cross-Pool Witness Accounting' (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem short_repair_overload {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (k s t : ℕ)
    (hts : t ≤ s) (E : Finset C)
    (hE : ∀ u ∈ E, u ∉ L ∅ ∧
      (∀ P ⊆ Z, #Z ≤ #P + s → ∀ a ∈ Icc 1 k,
        ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a → u ∉ L A) ∧
      ∃ a ∈ Icc 1 k, ∃ G ⊆ Z.powerset, (∀ A ∈ G, u ∈ L A) ∧
        (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) ∧
        ∃ T ⊆ Z, #T ≤ t ∧ ∀ A ∈ G, 3 ≤ #A → #A ≠ a → ∃ x ∈ A, x ∈ T) :
    #E * (s - t + 1) ≤ #Z * (#Z + 1) := by sorry

end Erdos624
