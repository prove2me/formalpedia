-- Prove2me | Theorems.Thm_Erdos624_trackBad_zero_iff
-- name    : Erdos624.trackBad_zero_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:07:59.582995+00:00
-- url     : https://prove2.me/theorems/6f10069c-1054-40c1-a95a-b0c8c3514f2d
-- title:
--   With one track, $\mathrm{TrackBad}(n,m,0)\iff H(n)>m$ (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By an earlier result, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** For $n\ge1$ and every $m$,
--
--   $$\mathrm{TrackBad}(n,m,0)\iff H(n)>m.$$
--
--   So the $s=0$ case of the track condition is exactly the statement that no map is $m$-good; together with `not_trackBad_of_H_le`, the track reformulation loses no strength and gains none.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B2a of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem trackBad_zero_iff {n m : ℕ} (hn : 0 < n) :
    (∀ g : Finset (Fin 0) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin 0), ∀ A ∈ Y.powerset, g B A ≠ u) ↔ m < H n := by sorry

end Erdos624
