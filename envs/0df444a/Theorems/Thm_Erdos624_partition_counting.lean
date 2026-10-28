-- Prove2me | Theorems.Thm_Erdos624_partition_counting
-- name    : Erdos624.partition_counting
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T05:30:41.371239+00:00
-- url     : https://prove2.me/theorems/6efb9f0b-6ed5-48b9-9341-8465337044b0
-- title:
--   Partition-counting lemma for t-subsets in one part (Erdős 624 auxiliary)
-- statement:
--   Let $q,t,N$ be positive integers and $c:\mathrm{Fin}\,q\to\mathbb N$ with $\sum_i c(i)=N$. If $N\ge q\,t(t+1)$, then
--
--   $$
--   \binom Nt\le 2\,q^{t-1}\sum_i\binom{c(i)}{t}.
--   $$
--
--   Thus a constant fraction of the $t$-subsets of a sufficiently large, arbitrarily partitioned set lie entirely in one part. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$.  This lemma does NOT settle Problem 624 / PAIR; it is an auxiliary partition-counting tool used toward a rank-deficiency bound.
--
--   **Formalization Note.** Pure natural-number statement over `Fin q → ℕ`; no dependence on the Erdős 624 definitions module.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (11) of the analysis derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
open Finset

namespace Erdos624

/-- Partition-counting lemma: a constant fraction of t-subsets lie in one part. -/
theorem partition_counting {q : ℕ} [NeZero q] (t N : ℕ) (c : Fin q → ℕ)
    (ht : 1 ≤ t) (hN : q * t * (t + 1) ≤ N) (hsum : ∑ i, c i = N) :
    N.choose t ≤ 2 * q ^ (t - 1) * ∑ i, (c i).choose t := by sorry

end Erdos624
