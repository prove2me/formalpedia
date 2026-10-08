-- Prove2me | Theorems.Thm_AdWordsMSVV_Tradeoff_lemma_5
-- name    : AdWordsMSVV.Tradeoff.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:18.891629+00:00
-- url     : https://prove2.me/theorems/28a4ffe3-326b-4945-b142-014a1a9cfd17
-- title:
--   Lemma 5, p. 10 — l = b + Δ(π, ψ)
-- statement:
--   Let $k\ge1$ and $N\ge0$ be integers and let $\alpha_1,\alpha_2,\dots$ and $\beta_1,\beta_2,\dots$ be real numbers with
--   $$\beta_i=\frac Nk-\frac{\alpha_1+\dots+\alpha_{i-1}}{k}\qquad(1\le i\le k),$$
--   so that $\beta_1=N/k$. Let $l=A\alpha$ and $b_i=(i/k)N$ as in the LP $L$. Then for every $1\le i\le k-1$,
--   $$\alpha_1\Bigl(1+\frac{i-1}{k}\Bigr)+\alpha_2\Bigl(1+\frac{i-2}{k}\Bigr)+\dots+\alpha_i=\frac{iN}{k}+(\alpha_1-\beta_1)+\dots+(\alpha_i-\beta_i),$$
--   that is, $l=b+\Delta$ with $\Delta_i=\sum_{j\le i}(\alpha_j-\beta_j)$.
--
--   The lemma relates the right-hand sides of $L$ and $L(\pi,\psi)$ in the proof of Theorem 8.
--
--   **Formalization Note** In the paper $\alpha_j$ is the number of bidders of type $j$, $\beta_i$ the money spent from slab $i$, and the relation for $\beta_i$ holds under the paper's simplifying assumption that bidders of type $j$ spend exactly $j/k$. It is therefore a hypothesis here, on arbitrary real sequences, and the lemma is the algebraic identity the paper's proof displays.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 10, Lemma 5 and its proof (displayed equation)

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

namespace AdWordsMSVV.Tradeoff
theorem lemma_5 (k N : ℕ) (hk : 1 ≤ k) (α β : ℕ → ℝ)
    (hβ : ∀ i ∈ Finset.Icc 1 k,
      β i = (N : ℝ) / k - (∑ j ∈ Finset.Icc 1 (i - 1), α j) / k) :
    ∀ i ∈ Finset.Icc 1 (k - 1),
      lVec k α i = bVec k N i + ∑ j ∈ Finset.Icc 1 i, (α j - β j) := by sorry
end AdWordsMSVV.Tradeoff
