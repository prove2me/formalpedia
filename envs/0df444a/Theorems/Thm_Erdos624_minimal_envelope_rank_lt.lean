-- Prove2me | Theorems.Thm_Erdos624_minimal_envelope_rank_lt
-- name    : Erdos624.minimal_envelope_rank_lt
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:42:29.619984+00:00
-- url     : https://prove2.me/theorems/a15764cd-b114-4960-8490-3102873782d9
-- title:
--   Coverage forces envelope rank $r\le k-1$ (corollary of (E), Erdős 624)
-- statement:
--   Setting: $U$ is a finite pool of inputs (to apply this to a sub-pool $V$, take $U$ to be the subtype $V$), $C$ a set of colours, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (e.g. $L(A)=\{g_0(A),g_1(A)\}$), $k\in\mathbb N$, and $u\in C$ with $u\notin L(\emptyset)$. A set $B$ is a *hole* if $u\notin L(A)$ for all $A\subseteq B$. $H_u=\{A: 0<|A|\le k,\ u\in L(A),\ u\notin L(A')\ \forall A'\subsetneq A\}$ (minimal witnesses of size $\le k$), $Z=\mathrm{span}_{\mathbb F_2}\{\chi_A: A\in H_u\}\le\mathbb F_2^U$, $Q=\mathbb F_2^U/Z$, $q_x=e_x+Z$, $r=\dim Q$, $\rho(B)=\dim\mathrm{span}\{q_x:x\in B\}$. All of these are written out inline in the Lean statement (no custom definitions).
--
--   **Corollary.** If every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$ (coverage of $u$), then $r<k$, i.e. $r\le k-1$. (For $k=0$ the hypotheses are contradictory, since $u\notin L(\emptyset)$.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem minimal_envelope_rank_lt {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A) :
    (Module.finrank (ZMod 2) ((U → ZMod 2) ⧸
      Submodule.span (ZMod 2) {v : U → ZMod 2 | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧
        (∀ A' ⊂ A, u ∉ L A') ∧ v = fun x => if x ∈ A then 1 else 0})) < k := by sorry

end Erdos624
