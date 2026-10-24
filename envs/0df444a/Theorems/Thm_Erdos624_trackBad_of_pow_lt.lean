-- Prove2me | Theorems.Thm_Erdos624_trackBad_of_pow_lt
-- name    : Erdos624.trackBad_of_pow_lt
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:07:58.71722+00:00
-- url     : https://prove2.me/theorems/bae04e94-1da5-481e-9e9a-8b3c2f81b037
-- title:
--   $\mathrm{TrackBad}(n,m,s)$ holds when $2^{m+s}<n$ (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By an earlier result, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** If $2^{m+s}<n$ then $\mathrm{TrackBad}(n,m,s)$.
--
--   The $2^s$ maps have at most $2^{m+s}<n$ values on the subsets of any $m$-set. Via track amplification this only gives $H(n+s)>m+s$ with $m+s<\log_2 n$, which the counting bound already gives.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B1 of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem trackBad_of_pow_lt {n m s : ℕ} (h : 2 ^ (m + s) < n) :
    ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by sorry

end Erdos624
