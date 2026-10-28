-- Prove2me | Theorems.Thm_Erdos624_rank_deficiency_labelling
-- name    : Erdos624.rank_deficiency_labelling
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T05:45:23.083981+00:00
-- url     : https://prove2.me/theorems/37f350e2-d0ab-4fa2-bed2-95e2075147a7
-- title:
--   Rank-deficiency labelling lemma with R=2^55, k₀=16 (Erdős 624 auxiliary)
-- statement:
--   For every integer $k\ge 16$ and every labelling $v:U\to\mathbb F_2^k$ on a finite set $U$ with $|U|=2^k$,
--
--   $$
--   \binom{2^k}{k-2}
--   \;\le\;
--   2^{55}\cdot
--   \Bigl|\bigl\{W\in\binom{U}{k-2}:
--   256\cdot|S_v(W)|\le 2^k\bigr\}\Bigr|,
--   $$
--
--   where $S_v(W)=\{\sum_{x\in A}v(x):A\subseteq W\}$ is the finite subset-sum image (equivalently the underlying set of $\operatorname{span}v(W)$). Equivalently, a positive-density fraction of the $(k-2)$-subsets satisfy $\dim\operatorname{span}v(W)\le k-8$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This lemma does NOT settle Problem 624 / PAIR; it only proves the rank-deficiency counting bound with explicit constants $R=2^{55}$ and $k_0=16$.
--
--   **Formalization Note.** Pure Mathlib statement: `U` is an arbitrary `Fintype` with `Fintype.card U = 2 ^ k`; $S_v(W)$ is written inline as `W.powerset.image (fun A => ∑ x ∈ A, v x)`. No dependence on the Erdős 624 definitions module.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (10)/(21) of the analysis derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
open Finset

namespace Erdos624

/-- Rank-deficiency labelling lemma: a 2^{-55} fraction of (k-2)-sets have dim ≤ k-8.
`S_v(W)` is the powerset-image of F₂ subset-sums. -/
theorem rank_deficiency_labelling {U : Type*} [Fintype U] [DecidableEq U]
    {k : ℕ} (hk : 16 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → Fin k → ZMod 2) :
    Nat.choose (2 ^ k) (k - 2) ≤
      2 ^ 55 *
        #{W ∈ powersetCard (k - 2) (univ : Finset U) |
          256 * #(W.powerset.image (fun A => ∑ x ∈ A, v x)) ≤ 2 ^ k} := by sorry

end Erdos624
