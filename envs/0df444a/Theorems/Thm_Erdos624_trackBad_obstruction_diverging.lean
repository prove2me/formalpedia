-- Prove2me | Theorems.Thm_Erdos624_trackBad_obstruction_diverging
-- name    : Erdos624.trackBad_obstruction_diverging
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:30:13.953476+00:00
-- url     : https://prove2.me/theorems/6831b912-49c3-462e-becf-afaf498e684d
-- title:
--   Track obstruction with diverging amplified gap (Erdős 624)
-- statement:
--   Let $H(n)$ be as in Erdős Problem 624. Say $\mathrm{TrackBad}(n,m,s)$ holds if for every family of maps $g_B:\mathcal P(U)\to U$ ($|U|=n$) indexed by the subsets $B$ of an $s$-set, there are $Y\subseteq U$ with $|Y|=m$ and $u\in U$ with $u\notin\{g_B(A):A\subseteq Y\}$ for every $B$. By `Erdos624.track_amplification`, $\mathrm{TrackBad}(n,m,s)$ implies $H(n+s)>m+s$ for $n\ge1$. **Theorem.** Let $k\ge1$ and let $s=\lfloor\log_2(k(k+1))\rfloor+1$, the least $s$ with $2^s>k(k+1)$. Then $\mathrm{TrackBad}(2^k,k,s)$ is false, although
--
--   $$k+s-\lceil\log_2(2^k+s)\rceil\ \ge\ \lfloor\log_2(k(k+1))\rfloor\to\infty.$$
--
--   So $m+s-\log_2(n+s)\to\infty$ alone does not imply $\mathrm{TrackBad}(n,m,s)$, even with only $O(\log\log n)$ tracks. (With $s\ge\log_2 n$ tracks this would be trivial, since constant tracks cover $U$.)
--
--   **Formalization Note.** The statement lists: $k(k+1)<2^s$; minimality of $s$; $\neg\mathrm{TrackBad}(2^k,k,s)$; and $\lfloor\log_2(k(k+1))\rfloor+\lceil\log_2(2^k+s)\rceil\le k+s$, using `Nat.log`/`Nat.clog`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; Claim B3 of claim from a GPT answer relayed by Ethan Cheung (third round, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem trackBad_obstruction_diverging (k : ℕ) (hk : 1 ≤ k) :
    k * (k + 1) < 2 ^ (Nat.log 2 (k * (k + 1)) + 1) ∧
    (∀ s' < (Nat.log 2 (k * (k + 1)) + 1), 2 ^ s' ≤ k * (k + 1)) ∧
    (¬ ∀ g : Finset (Fin (Nat.log 2 (k * (k + 1)) + 1)) → Finset (Fin (2 ^ k)) → Fin (2 ^ k), ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∃ u : Fin (2 ^ k), ∀ B : Finset (Fin (Nat.log 2 (k * (k + 1)) + 1)), ∀ A ∈ Y.powerset, g B A ≠ u) ∧
    Nat.log 2 (k * (k + 1)) + Nat.clog 2 (2 ^ k + (Nat.log 2 (k * (k + 1)) + 1)) ≤ k + (Nat.log 2 (k * (k + 1)) + 1) := by sorry

end Erdos624
