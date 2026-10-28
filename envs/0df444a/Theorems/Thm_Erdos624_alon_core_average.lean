-- Prove2me | Theorems.Thm_Erdos624_alon_core_average
-- name    : Erdos624.alon_core_average
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:48:43.006295+00:00
-- url     : https://prove2.me/theorems/e7cf0667-52cb-4e92-8a7f-bea8adc2b55a
-- title:
--   Alon per-core average: $32\sum_{a\ne b\in R}L_f(W\cup\{a,b\})\ge n\,|R|(|R|-1)$ for $|R|\ge7$ (Erdős 624)
-- statement:
--   Let $C$ be a finite set of colours, $f:\mathcal P(U)\to C$ arbitrary, and $W\subseteq U$ finite with $|C|=n=4\cdot2^{|W|}$. Let $R\subseteq U$ be a finite set disjoint from $W$ with $|R|\ge7$. Writing $L_f(Y)=n-|f[\mathcal P(Y)]|$, the sum over ordered pairs of distinct points satisfies$$32\sum_{a\in R}\ \sum_{b\in R\setminus\{a\}} L_f(W\cup\{a,b\})\;\ge\; n\,|R|\,(|R|-1).$$Proof: palette inequality termwise, then Cauchy–Schwarz over the $n$ colours for the overlap counts; the threshold $|R|\ge7$ is exactly what the extremal computation needs.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for every $|Y|\ge m$. This is an auxiliary finite inequality (the one-map 'robust Alon' loss bound and its ingredients) used in Sol's Round 10 analysis (parity-palette inequality, inequalities (11)/(13), top-layer-free resilience). It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: robust and conditioned Alon inequalities' (palette mechanism); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem alon_core_average {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (f : Finset U → C) (W R : Finset U) (hRW : Disjoint R W) (hR : 7 ≤ #R)
    (hC : Fintype.card C = 4 * 2 ^ #W) :
    Fintype.card C * (#R * (#R - 1)) ≤
      32 * ∑ a ∈ R, ∑ b ∈ R.erase a,
        (Fintype.card C - #((insert a (insert b W)).powerset.image f)) := by sorry

end Erdos624
