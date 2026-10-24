-- Prove2me | Theorems.Thm_Erdos624_not_trackBad_count
-- name    : Erdos624.not_trackBad_count
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:08:05.80658+00:00
-- url     : https://prove2.me/theorems/4a746d68-f72f-45c4-a17c-df7ab9d3e5a8
-- title:
--   Counting obstruction to $\mathrm{TrackBad}(n,m,s)$ (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By an earlier result, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** If
--
--   $$n\binom{n}{m}(n-1)^{2^{m+s}}<n^{2^{m+s}},$$
--
--   then $\mathrm{TrackBad}(n,m,s)$ is false: some family of $2^s$ maps $g_B:\mathcal P(U)\to U$ has no common omitted value on any $m$-set.
--
--   Proof by double counting (the first-moment method for uniformly random maps): for fixed $Y,u$ exactly a $(1-1/n)^{2^{m+s}}$ fraction of all families omit $u$ on $Y$ in all tracks, and there are $\binom nm n$ pairs $(Y,u)$.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B2b of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026) (sharpened to the exact counting hypothesis)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem not_trackBad_count {n m s : ℕ}
    (h : n * n.choose m * (n - 1) ^ (2 ^ (m + s)) < n ^ (2 ^ (m + s))) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by sorry

end Erdos624
