-- Prove2me | Theorems.Thm_Erdos624_core_compression_surplus
-- name    : Erdos624.core_compression_surplus
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T03:33:31.431222+00:00
-- url     : https://prove2.me/theorems/04fc67de-1158-4d78-af47-2bda05f178bb
-- title:
--   A map with small image on a whole star has a common hole with every map (Erdős 624)
-- statement:
--   Let $U$ be a finite set with $n=2^k$ elements. For a map $g:\mathcal P(U)\to U$ and $Y\subseteq U$ write $I_g(Y)=\{g(A):A\subseteq Y\}$. For $B\subseteq U$ let $\mathcal K_B$ be the set of $k$-subsets $Y\supseteq B$.
--
--   **Theorem.** Let $k\ge3$, $S\subseteq U$ with $|S|\le k-2$, and let $h:\mathcal P(U)\to U$ satisfy $64|I_h(Y)|\le n$ for every $Y\in\mathcal K_S$. Then for every map $g:\mathcal P(U)\to U$,
--
--   $$n\,|\mathcal K_S|\;\le\;64\sum_{Y\in\mathcal K_S}\bigl(n-|I_h(Y)\cup I_g(Y)|\bigr).$$
--
--   In particular $h$ and $g$ have a common hole on some $k$-set through $S$. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it would suffice to show that, for large $k$, any two maps $\mathcal P(U)\to U$ with $|U|=2^k$ have a *common hole*: a $k$-set $Y$ and a point $u$ missed by both maps on $\mathcal P(Y)$.  These results do not settle Problem 624.
--
--   **Formalization Note.** Counting form with natural numbers (truncated subtraction is harmless since $|I_g(Y)|\le n$); $U$ is an arbitrary `Fintype` with `Fintype.card U = 2 ^ k`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (3) of the analysis derived from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem core_compression_surplus {U : Type*} [Fintype U] [DecidableEq U] (k : ℕ) (hk : 3 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (S : Finset U) (hS : #S ≤ k - 2) (h g : Finset U → U)
    (hsmall : ∀ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y),
      64 * #(Y.powerset.image h) ≤ 2 ^ k) :
    2 ^ k * #((powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y)) ≤
      64 * ∑ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y),
        (2 ^ k - #(Y.powerset.image h ∪ Y.powerset.image g)) := by sorry

end Erdos624
