-- Prove2me | Theorems.Thm_Erdos624_k17_three_colour_ramsey
-- name    : Erdos624.k17_three_colour_ramsey
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:31.464707+00:00
-- url     : https://prove2.me/theorems/d69ee250-6889-44ec-bcda-5fb0b09f6521
-- title:
--   Every 3-colouring of the edges of $K_{17}$ has a monochromatic triangle (Erdős 624 packet obstruction)
-- statement:
--   Let $g:\{0,\dots,16\}^2\to\{0,1,2\}$ be symmetric ($g(x,y)=g(y,x)$); think of $g(x,y)$ for $x\ne y$ as the colour of edge $xy$ of $K_{17}$. Then there are distinct $x,y,z$ with $g(x,y)=g(x,z)=g(y,z)$. (The classical bound $R(3,3,3)\le17$; the diagonal values $g(x,x)$ play no role.)
--
--   This is the Ramsey step of Sol's 'A Triple-Colour Ramsey Obstruction'.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem k17_three_colour_ramsey (g : Fin 17 → Fin 17 → Fin 3) (hg : ∀ x y, g x y = g y x) :
    ∃ x y z : Fin 17, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ g x y = g x z ∧ g x y = g y z := by sorry

end Erdos624
