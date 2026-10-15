-- Prove2me | Theorems.Thm_CommitteeVoting_SingleVoter_lemma_1
-- name    : CommitteeVoting.SingleVoter.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:28.244434+00:00
-- url     : https://prove2.me/theorems/dc2c5ec1-710a-40e4-9701-1b5d92c04350
-- title:
--   Lemma 1, p. 19 — for p₁ ≥ ⋯ ≥ p_m, the top k parameters maximise Pr[X_P > x] over k-subsets
-- statement:
--   Let $m \ge k$ and let $p_1 \ge p_2 \ge \dots \ge p_m$ be numbers in $[0,1]$. For a set $P = \{j_1, \dots, j_k\}$ of $k$ indices, let $X_P$ be Poisson binomial with parameters $(p_{j_1}, \dots, p_{j_k})$. Then for every positive integer $x$ and every such $P$,
--
--   $$
--   \Pr[X_P > x] \;\le\; \Pr[X_{\{1,\dots,k\}} > x],
--   $$
--
--   i.e. the first $k$ parameters attain $\max_{P} \Pr[X_P > x]$ over all $k$-element index sets.
--
--   Read with $p_j = s_j$ the posterior honesty probabilities, this says that the committee of the $k$ candidates most likely to be honest maximises the probability of having more than $x$ honest members; Proposition 2 rests on it.
--
--   **Formalization Note** The paper writes $\operatorname{argmax}_{P} \Pr[X_P > x] = \{p_1, \dots, p_k\}$. When parameters tie, the argmax is not a single set (if all $p_j$ are equal, every $k$-subset maximises), so the statement is formalized as "$\{1,\dots,k\}$ attains the maximum". $P$ ranges over $k$-element sets of indices (the parameters may repeat). The hypothesis $x > 0$ is kept as printed; the printed requirement that $m$ and $k$ be positive is dropped, since for $k = 0$ both sides are $0$. Indices are 0-based: the first $k$ indices are $\{j : j < k\}$, and $p_1 \ge \dots \ge p_m$ is antitonicity on $\{0, \dots, m-1\}$.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 19, Lemma 1

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace CommitteeVoting.SingleVoter

/-- Lemma 1 (p. 19): if the probabilities `p j` are non-increasing in `j` and `0 < x`, then among all
`k`-element index sets `S`, the first `k` indices maximise the Poisson binomial tail
`Pr[X_S > x]` (they attain the argmax). -/
theorem lemma_1 {m k : ℕ} (hkm : k ≤ m) (p : Fin m → ℝ) (hanti : Antitone p)
    (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (x : ℕ) (hx : 0 < x)
    (S : Finset (Fin m)) (hS : S.card = k) :
    pbTail p S x ≤ pbTail p (Finset.univ.filter fun j : Fin m => j.val < k) x := by sorry

end CommitteeVoting.SingleVoter
