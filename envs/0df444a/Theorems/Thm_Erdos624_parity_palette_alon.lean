-- Prove2me | Theorems.Thm_Erdos624_parity_palette_alon
-- name    : Erdos624.parity_palette_alon
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:58:58.625962+00:00
-- url     : https://prove2.me/theorems/82847bc9-e1fa-4486-9414-66917b07fd06
-- title:
--   Parity-palette inequality: $32\sum_{Y\in\binom Vk}(n-|J_\varepsilon(Y)|)\ge n\binom Nk$ for $N\ge k+5$ (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ are two arbitrary maps (a *pair*); write $L(A)=\{g_0(A),g_1(A)\}$ for the list of colours at the input $A$. For $\varepsilon\in\{0,1\}$ and finite $Y$ define the parity-restricted palette $J_\varepsilon(Y)=\bigcup_{A\subseteq Y,\ |A|\equiv\varepsilon\ (2)}L(A)$. Let $k\ge3$ and let $V\subseteq U$ with $N=|V|\ge k+5$. Then$$32\sum_{Y\in\binom Vk}\bigl(n-|J_\varepsilon(Y)|\bigr)\;\ge\; n\binom Nk.$$(The Lean statement allows any natural number $\varepsilon$, the condition being $|A|\bmod 2=\varepsilon$; for $\varepsilon\ge2$ the palette is empty and the bound is trivial.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it suffices to find common holes for fixed numbers of tracks; this is an auxiliary finite inequality from Sol's Round 10 analysis of the two-track case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 reports (consolidated report §'parity transport', §'many holes one level below'; Step 17 report 'resilient relations below the top layer', eqs. (9)-(26)); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem parity_palette_alon {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (V : Finset U) (hV : k + 5 ≤ #V) (ε : ℕ) :
    2 ^ k * #(powersetCard k V) ≤
      32 * ∑ Y ∈ powersetCard k V,
        (2 ^ k - #((Y.powerset.filter (fun A => #A % 2 = ε)).biUnion
          (fun A => ({g0 A, g1 A} : Finset C)))) := by sorry

end Erdos624
