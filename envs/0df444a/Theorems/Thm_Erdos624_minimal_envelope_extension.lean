-- Prove2me | Theorems.Thm_Erdos624_minimal_envelope_extension
-- name    : Erdos624.minimal_envelope_extension
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:42:31.561092+00:00
-- url     : https://prove2.me/theorems/a85cb043-aa6c-4fe5-847d-f1982c2b810c
-- title:
--   Minimal-envelope extension (E): a hole $B$ with $|B|\le k$ extends to a hole of size $\min(k,\,r+|B|-\rho(B))$ (Erdős 624)
-- statement:
--   Setting: $U$ is a finite pool of inputs (to apply this to a sub-pool $V$, take $U$ to be the subtype $V$), $C$ a set of colours, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (e.g. $L(A)=\{g_0(A),g_1(A)\}$), $k\in\mathbb N$, and $u\in C$ with $u\notin L(\emptyset)$. A set $B$ is a *hole* if $u\notin L(A)$ for all $A\subseteq B$. $H_u=\{A: 0<|A|\le k,\ u\in L(A),\ u\notin L(A')\ \forall A'\subsetneq A\}$ (minimal witnesses of size $\le k$), $Z=\mathrm{span}_{\mathbb F_2}\{\chi_A: A\in H_u\}\le\mathbb F_2^U$, $Q=\mathbb F_2^U/Z$, $q_x=e_x+Z$, $r=\dim Q$, $\rho(B)=\dim\mathrm{span}\{q_x:x\in B\}$. All of these are written out inline in the Lean statement (no custom definitions).
--
--   **Theorem (E).** If $B$ is a hole with $|B|\le k$, then there is a hole $B'\supseteq B$ with $|B'|=\min\bigl(k,\ r+(|B|-\rho(B))\bigr)$. (Lean uses natural-number subtraction $|B|-\rho(B)$; this is harmless since $\rho(B)\le|B|$ always.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem minimal_envelope_extension {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (B : Finset U) (hB : #B ≤ k) (hBhole : ∀ A ⊆ B, u ∉ L A) :
    ∃ B' : Finset U, B ⊆ B' ∧ (∀ A ⊆ B', u ∉ L A) ∧
      #B' = min k ((Module.finrank (ZMod 2) ((U → ZMod 2) ⧸
      Submodule.span (ZMod 2) {v : U → ZMod 2 | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧
        (∀ A' ⊂ A, u ∉ L A') ∧ v = fun x => if x ∈ A then 1 else 0})) +
        (#B - Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((fun x => (Submodule.span (ZMod 2) {v : U → ZMod 2 | ∃ A : Finset U, 0 < #A ∧ #A ≤ k ∧ u ∈ L A ∧
        (∀ A' ⊂ A, u ∉ L A') ∧ v = fun x => if x ∈ A then 1 else 0}).mkQ (Pi.single x 1)) '' (B : Set U))))) := by sorry

end Erdos624
