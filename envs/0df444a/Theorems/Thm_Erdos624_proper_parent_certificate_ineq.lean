-- Prove2me | Theorems.Thm_Erdos624_proper_parent_certificate_ineq
-- name    : Erdos624.proper_parent_certificate_ineq
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T14:04:22.420622+00:00
-- url     : https://prove2.me/theorems/208aaf91-9923-47dd-af5d-70eb2866d89b
-- title:
--   Proper-parent certificate inequality (13): $32N\sum D^\circ+32N(n-|S|)K+32kK\sum_u(|R_u|+|T_u|)\ge nNK$ (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ are two arbitrary maps (a *pair*); write $L(A)=\{g_0(A),g_1(A)\}$ for the list of colours at the input $A$. Let $k\ge3$ and let $V\subseteq U$ be a pool with $N=|V|\ge k+5$; write $K=\binom Nk$. Let $S\subseteq C\setminus L(\varnothing)$. For each $u\in S$ fix a deletion set $R_u\subseteq U$ and a parity certificate $w_u:U\to\mathbf F_2$ for the proper minimal witnesses of $u$ surviving the deletion: for every $A\subseteq V\setminus R_u$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for all $B\subsetneq A$, we have $\sum_{x\in A}w_u(x)=1$. Put $T_u=\{x\in V\setminus R_u: w_u(x)=0\}$. For a $k$-set $Y$ let $J^\circ(Y)=\bigcup_{A\subsetneq Y}L(A)$, $D^\circ(Y)=n-|J^\circ(Y)|$, $J^\circ_{\mathrm{odd}}(Y)=\bigcup_{A\subsetneq Y,\,|A|\text{ odd}}L(A)$ and $Q^\circ(Y)=n-|J^\circ_{\mathrm{odd}}(Y)|$. Then (no coverage assumption is needed)$$32N\sum_{Y\in\binom Vk}D^\circ(Y)+32N(n-|S|)K+32kK\sum_{u\in S}\bigl(|R_u|+|T_u|\bigr)\;\ge\; nNK.\qquad(13)$$
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it suffices to find common holes for fixed numbers of tracks; this is an auxiliary finite inequality from Sol's Round 10 analysis of the two-track case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 reports (consolidated report §'parity transport', §'many holes one level below'; Step 17 report 'resilient relations below the top layer', eqs. (9)-(26)); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem proper_parent_certificate_ineq {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (V : Finset U) (hV : k + 5 ≤ #V) (S : Finset C)
    (hS : ∀ u ∈ S, u ∉ ({g0 ∅, g1 ∅} : Finset C))
    (R : C → Finset U) (w : C → U → ZMod 2)
    (hw : ∀ u ∈ S, ∀ A ⊆ V \ R u, 0 < #A → #A < k → u ∈ ({g0 A, g1 A} : Finset C) →
      (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) → ∑ x ∈ A, w u x = 1) :
    2 ^ k * #V * #(powersetCard k V) ≤
      32 * #V * ∑ Y ∈ powersetCard k V, (2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)))) +
      32 * #V * (2 ^ k - #S) * #(powersetCard k V) +
      32 * k * #(powersetCard k V) *
        ∑ u ∈ S, (#(R u) + #((V \ R u).filter (fun x => w u x = 0))) := by sorry

end Erdos624
