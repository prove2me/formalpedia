-- Prove2me | Theorems.Thm_Erdos624_alon_palette_inequality
-- name    : Erdos624.alon_palette_inequality
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:48:41.267841+00:00
-- url     : https://prove2.me/theorems/689b21f2-58d0-4d4c-b400-9e7fdf443638
-- title:
--   Alon palette inequality: $L_f(W\cup\{a,b\})\ge d_a+d_b+|S_a\cap S_b|$ (Erdős 624)
-- statement:
--   Let $C$ be a finite set of colours and $f:\mathcal P(U)\to C$ an arbitrary map on the finite subsets of a set $U$. Let $W\subseteq U$ be finite with $|C|=4\cdot 2^{|W|}$ (in the application $|W|=k-2$ and $|C|=n=2^k$, so $q:=2^{|W|}=n/4$). For $a\notin W$ define the palette $$S_a=\{f(A\cup\{a\}):A\subseteq W\},\qquad d_a=q-|S_a|\ge0.$$ Then for distinct $a,b\notin W$, writing $L_f(Y)=|C|-|f[\mathcal P(Y)]|$,$$L_f(W\cup\{a,b\})\;\ge\; d_a+d_b+|S_a\cap S_b|.$$Proof idea: $\mathcal P(W\cup\{a,b\})$ splits into four blocks of size $q$; two of them contribute at most $2q$ colours and the two one-point blocks contribute exactly $S_a\cup S_b$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for every $|Y|\ge m$. This is an auxiliary finite inequality (the one-map 'robust Alon' loss bound and its ingredients) used in Sol's Round 10 analysis (parity-palette inequality, inequalities (11)/(13), top-layer-free resilience). It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 consolidated report, section 'Proved: robust and conditioned Alon inequalities' (palette mechanism); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem alon_palette_inequality {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (f : Finset U → C) (W : Finset U) (a b : U) (hab : a ≠ b) (ha : a ∉ W) (hb : b ∉ W)
    (hC : Fintype.card C = 4 * 2 ^ #W) :
    (2 ^ #W - #(W.powerset.image (fun A => f (insert a A)))) +
        (2 ^ #W - #(W.powerset.image (fun A => f (insert b A)))) +
        #(W.powerset.image (fun A => f (insert a A)) ∩ W.powerset.image (fun A => f (insert b A))) ≤
      Fintype.card C - #((insert a (insert b W)).powerset.image f) := by sorry

end Erdos624
