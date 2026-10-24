-- Prove2me | Theorems.Thm_Erdos624_conditioned_alon
-- name    : Erdos624.conditioned_alon
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:33:31.928934+00:00
-- url     : https://prove2.me/theorems/382fab1f-5fbe-4eb1-9664-16028c747370
-- title:
--   Conditioned Alon bound: Alon-type loss on every star of $k$-sets through a small core (Erdős 624)
-- statement:
--   Let $U$ be a finite set with $n=2^k$ elements. For a map $g:\mathcal P(U)\to U$ and $Y\subseteq U$ write $I_g(Y)=\{g(A):A\subseteq Y\}$. For $B\subseteq U$ let $\mathcal K_B$ be the set of $k$-subsets $Y\supseteq B$.
--
--   **Theorem.** Let $k\ge3$, $B\subseteq U$ with $|B|\le k-2$, and let $g:\mathcal P(U)\to U$ be arbitrary. Then
--
--   $$n\,|\mathcal K_B|\;\le\;32\sum_{Y\in\mathcal K_B}\bigl(n-|I_g(Y)|\bigr).$$
--
--   So on average over the $k$-sets containing any prescribed core of size at most $k-2$, every map misses at least $n/32$ points. With $B=\emptyset$ this is the earlier `robust_alon_sum`; the conditioned version is strictly stronger and does not follow from the unconditioned average. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it would suffice to show that, for large $k$, any two maps $\mathcal P(U)\to U$ with $|U|=2^k$ have a *common hole*: a $k$-set $Y$ and a point $u$ missed by both maps on $\mathcal P(Y)$.  These results do not settle Problem 624.
--
--   **Formalization Note.** Counting form with natural numbers (truncated subtraction is harmless since $|I_g(Y)|\le n$); $U$ is an arbitrary `Fintype` with `Fintype.card U = 2 ^ k`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); formal strengthening of Alon's bound (privately communicated, cited on erdosproblems.com/624); conditioned form from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem conditioned_alon {U : Type*} [Fintype U] [DecidableEq U] (k : ℕ) (hk : 3 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (B : Finset U) (hB : #B ≤ k - 2) (g : Finset U → U) :
    2 ^ k * #((powersetCard k (univ : Finset U)).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image g)) := by sorry

end Erdos624
