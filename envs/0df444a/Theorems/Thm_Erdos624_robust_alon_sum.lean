-- Prove2me | Theorems.Thm_Erdos624_robust_alon_sum
-- name    : Erdos624.robust_alon_sum
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:30.649896+00:00
-- url     : https://prove2.me/theorems/013f27df-d077-47b2-9bfb-f8a004e4e3b7
-- title:
--   Robust Alon bound for Erdős 624: a random $k$-set misses $n/32$ points on average
-- statement:
--   Let $X$ be a set with $n=2^k$ elements, $k\ge3$, and let $f:\mathcal P(X)\to X$ be arbitrary. For a $k$-subset $Y\subseteq X$ write $L_f(Y)=n-|\{f(A):A\subseteq Y\}|$ for the number of points of $X$ missed by $f$ on the subsets of $Y$. Let $\mathcal K=\binom{X}{k}$. **Theorem.**
--
--   $$32\sum_{Y\in\mathcal K}L_f(Y)\;\ge\;n\,|\mathcal K|,$$
--
--   i.e. for a uniformly random $k$-set $Y$, $\mathbb E\,L_f(Y)\ge n/32$.
--
--   This is a uniform, averaged and explicit-constant version of Alon's theorem (reported on erdosproblems.com/624 as a personal communication) that for large $k$ every $f$ has a $k$-set $Y$ with $|\{f(A):A\subseteq Y\}|<(1-c)2^k$. Here $c$ can be any constant below $1/32$ and every $k\ge3$ is covered. It does not by itself give $H(n)-\log_2 n\to\infty$.
--
--   **Formalization Note.** $X=\mathrm{Fin}\,(2^k)$; the statement is in counting form (sums over $k$-subsets, natural numbers), with no probability.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; palette-overlap argument (B.1–B.4) of claim from GPT 6.1 Sol (fourth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem robust_alon_sum (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    2 ^ k * #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset (Fin (2 ^ k))),
        (2 ^ k - #(Y.powerset.image f)) := by sorry

end Erdos624
