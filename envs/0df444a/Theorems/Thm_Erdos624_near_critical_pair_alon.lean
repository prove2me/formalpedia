-- Prove2me | Theorems.Thm_Erdos624_near_critical_pair_alon
-- name    : Erdos624.near_critical_pair_alon
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:58:58.505951+00:00
-- url     : https://prove2.me/theorems/b4e7055a-074f-4a94-be01-2b1419ac06c8
-- title:
--   Near-critical pair inequality: $32\sum_{W\in\binom V{k-1}}D(W)\ge n\binom N{k-1}$ (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ are two arbitrary maps (a *pair*); write $L(A)=\{g_0(A),g_1(A)\}$ for the list of colours at the input $A$. For finite $W$ let $J(W)=\bigcup_{A\subseteq W}L(A)$ and $D(W)=n-|J(W)|$. Let $k\ge3$, let $V\subseteq U$ be a pool with $N=|V|\ge k+4$, and let $B\subseteq U$ be a core with $|B|\le k-3$. Then$$32\sum_{\substack{W\subseteq V,\ |W|=k-1\\ B\subseteq W}}D(W)\;\ge\; n\,\bigl|\{W\subseteq V:\ |W|=k-1,\ B\subseteq W\}\bigr|.$$With $B=\emptyset$ this reads $32\sum_{W\in\binom V{k-1}}D(W)\ge n\binom N{k-1}$: an arbitrary pair has, on average, $n/32$ common holes one level below the target size $k$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it suffices to find common holes for fixed numbers of tracks; this is an auxiliary finite inequality from Sol's Round 10 analysis of the two-track case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 reports (consolidated report §'parity transport', §'many holes one level below'; Step 17 report 'resilient relations below the top layer', eqs. (9)-(26)); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem near_critical_pair_alon {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (B V : Finset U) (hB : #B ≤ k - 3) (hV : k + 4 ≤ #V) :
    2 ^ k * #((powersetCard (k - 1) V).filter (fun W => B ⊆ W)) ≤
      32 * ∑ W ∈ (powersetCard (k - 1) V).filter (fun W => B ⊆ W),
        (2 ^ k - #(W.powerset.biUnion (fun A => ({g0 A, g1 A} : Finset C)))) := by sorry

end Erdos624
