-- Prove2me | Theorems.Thm_Erdos624_not_trackBad_pow
-- name    : Erdos624.not_trackBad_pow
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:11.853389+00:00
-- url     : https://prove2.me/theorems/1b5e3ed0-3d09-47d7-8903-130b8fcd3dc9
-- title:
--   $\mathrm{TrackBad}(2^k,k,s)$ fails once $2^s>k(k+1)$ (Erdős 624)
-- statement:
--   Let $H(n)$ be as in Erdős Problem 624. Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By `Erdos624.track_amplification`, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** If $k\ge1$ and $k(k+1)<2^s$, then $\mathrm{TrackBad}(2^k,k,s)$ is false: some family of $2^s$ maps on $2^k$ points has no common omitted value on any $k$-set.
--
--   With $n=2^k$, $r=2^s$: $2(n-1)^n\le n^n$ gives $n\binom nk(n-1)^{nr}\le 2^{k(k+1)}(n-1)^{nr}<2^r(n-1)^{nr}\le n^{nr}$, and the counting obstruction `Erdos624.not_trackBad_count` applies.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,n$ and the $s$-set is $\mathrm{Fin}\,s$, as in `Erdos624.track_amplification`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B3 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem not_trackBad_pow (k s : ℕ) (hk : 1 ≤ k) (hs : k * (k + 1) < 2 ^ s) :
    ¬ ∀ g : Finset (Fin s) → Finset (Fin (2 ^ k)) → Fin (2 ^ k), ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∃ u : Fin (2 ^ k), ∀ B : Finset (Fin s), ∀ A ∈ Y.powerset, g B A ≠ u := by sorry

end Erdos624
