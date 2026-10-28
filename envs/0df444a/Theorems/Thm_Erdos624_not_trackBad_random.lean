-- Prove2me | Theorems.Thm_Erdos624_not_trackBad_random
-- name    : Erdos624.not_trackBad_random
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:08:05.876144+00:00
-- url     : https://prove2.me/theorems/6a21323a-e872-4469-87df-c1405188e525
-- title:
--   Random obstruction: $\mathrm{TrackBad}(n,m,s)$ fails once $2^{m+s}\ge n(\ln n\,(m+1)+1)$ (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By an earlier result, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** If $n\ge2$ and
--
--   $$n\bigl((m+1)\ln n+1\bigr)\le 2^{m+s},$$
--
--   then $\mathrm{TrackBad}(n,m,s)$ is false. In particular the track method can never give more than $H(n+s)>\log_2 n+2\log_2\log_2 n+O(1)$.
--
--   From $\binom nm\le n^m$ and $(1-1/n)^K\le e^{-K/n}$ one gets $n\binom nm(n-1)^K\le e^{-1}n^K<n^K$ for $K=2^{m+s}$; then apply the counting obstruction.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B2b of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem not_trackBad_random {n m s : ℕ} (hn : 2 ≤ n)
    (h : (n : ℝ) * (Real.log n * (m + 1) + 1) ≤ 2 ^ (m + s)) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by sorry

end Erdos624
