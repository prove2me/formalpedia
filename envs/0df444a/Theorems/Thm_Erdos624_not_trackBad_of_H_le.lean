-- Prove2me | Theorems.Thm_Erdos624_not_trackBad_of_H_le
-- name    : Erdos624.not_trackBad_of_H_le
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:08:07.476803+00:00
-- url     : https://prove2.me/theorems/fbfeb466-2209-4e0b-ae98-08d5b0e2f649
-- title:
--   $H(n+s)\le m+s$ implies that $\mathrm{TrackBad}(n,m,s)$ fails (Erdős 624)
-- statement:
--   Let $H(n)$ be the least $m$ such that some $f:\mathcal P(X)\to X$, $|X|=n$, satisfies $\{f(A):A\subseteq Y\}=X$ for all $Y\subseteq X$ with $|Y|\ge m$ (Erdős Problem 624). Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By an earlier result, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** If $n\ge1$ and $H(n+s)\le m+s$ then $\mathrm{TrackBad}(n,m,s)$ is false.
--
--   This is the contrapositive of track amplification: the track condition is never stronger than the target bound $H(n+s)>m+s$ itself.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B2a of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem not_trackBad_of_H_le {n m s : ℕ} (hn : 0 < n) (h : H (n + s) ≤ m + s) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin n) → Fin n, ∃ Y : Finset (Fin n), #Y = m ∧
      ∃ u : Fin n, ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by sorry

end Erdos624
