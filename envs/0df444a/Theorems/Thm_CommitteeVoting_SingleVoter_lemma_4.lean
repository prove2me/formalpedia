-- Prove2me | Theorems.Thm_CommitteeVoting_SingleVoter_lemma_4
-- name    : CommitteeVoting.SingleVoter.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:29.357977+00:00
-- url     : https://prove2.me/theorems/a21df425-1913-4c65-b67e-2f1f09a26300
-- title:
--   Lemma 4, p. 49 — the Poisson binomial law is invariant under permuting its parameters
-- statement:
--   Let $p_1, \dots, p_n$ be the parameters of a Poisson binomial random variable $X$ and let $\sigma$ be a permutation of $\{1,\dots,n\}$. Let $X'$ be Poisson binomial with the permuted parameters $p_{\sigma(1)}, \dots, p_{\sigma(n)}$. Then for every $\ell \in \{0, \dots, n\}$,
--
--   $$
--   \Pr[X = \ell] = \Pr[X' = \ell].
--   $$
--
--   The law of a sum of independent Bernoulli variables depends only on the multiset of their parameters; Lemma 1's proof uses this to reorder the parameters of a committee.
--
--   **Formalization Note** The paper writes the permuted parameters as "$\sigma(p_1), \dots, \sigma(p_n)$"; this means $p_{\sigma(1)}, \dots, p_{\sigma(n)}$ and is stated so. The identity is algebraic and is stated without assuming $0 \le p_i \le 1$ (the printed lemma's parameters are probabilities, so the printed lemma is the special case). Indices are 0-based.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 49, Lemma 4

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace CommitteeVoting.SingleVoter

/-- Lemma 4 (p. 49): permuting the parameters of a Poisson binomial law leaves its probability mass
function unchanged. -/
theorem lemma_4 {n : ℕ} (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    pbPMF p Finset.univ ℓ = pbPMF (p ∘ σ) Finset.univ ℓ := by sorry

end CommitteeVoting.SingleVoter
