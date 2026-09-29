-- Prove2me | Theorems.Thm_CandesTao_LowerBound_all_rows_sampled_prob
-- name    : CandesTao.LowerBound.all_rows_sampled_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:44:06.925057+00:00
-- url     : https://prove2.me/theorems/a9968a66-01e2-4d17-94d6-a2f280f606a1
-- title:
--   Section II — by independence, all rows are sampled with probability $(1-\pi)^n$
-- statement:
--   Consider the Bernoulli sampling model on the entries of an $n\times n$ matrix: each entry $(i,j)$ belongs to the random observation set $\Omega$ independently with probability $p \in [0,1]$. Let $S_1,\dots,S_n$ be pairwise disjoint sets of entries, each of cardinality $\ell$ (for example, the $n$ rows, with $\ell = n$, or one row of one diagonal block for each of the $n$ rows, with block width $\ell$). Then the probability that every $S_a$ contains at least one observed entry is
--
--   $$\mathbb{P}\bigl(\Omega \cap S_a \neq \emptyset \text{ for all } a = 1,\dots,n\bigr) = \bigl(1 - (1-p)^{\ell}\bigr)^{n}.$$
--
--   Each $S_a$ is unsampled with probability $\pi = (1-p)^{\ell}$, and the $n$ events are independent because the sets are disjoint. In the lower-bound argument of Candès and Tao this computes the probability $(1-\pi_0)^n$ (rows, $\pi_0 = (1-p)^n$) and $(1-\pi_1)^n$ (rows of diagonal blocks, $\pi_1 = (1-p)^\ell$) that every relevant row is sampled.
--
--   **Formalization Note** The probability is the platform's `bernoulliEventProb p`, the sum over all subsets $\Omega$ of the weight $p^{|\Omega|}(1-p)^{n^2-|\Omega|}$.
-- source:
--   Candès & Tao, The Power of Convex Relaxation: Near-Optimal Matrix Completion, IEEE Trans. Inf. Theory 56(5), 2010, p. 2059, Section II ('By independence, the probability that all rows are sampled at least once is (1 − π₀)^n') and p. 2060 (π₁ = (1 − p)^ℓ for a fixed row of a fixed block)

import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion

namespace CandesTao.LowerBound

theorem all_rows_sampled_prob (n ℓ : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Fin n → Finset (Fin n × Fin n))
    (hdisj : Pairwise (fun a b => Disjoint (S a) (S b)))
    (hcard : ∀ a, (S a).card = ℓ) :
    bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => ∀ a, ∃ e ∈ S a, e ∈ Ω) =
      (1 - (1 - p) ^ ℓ) ^ n := by sorry

end CandesTao.LowerBound
