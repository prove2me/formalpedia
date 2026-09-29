-- Prove2me | Theorems.Thm_ABOThreshold_bad_norm_recursion
-- name    : ABOThreshold.bad_norm_recursion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T11:42:21.336271+00:00
-- url     : https://prove2.me/theorems/c0e4b6a4-b804-4744-b053-ec48e1bae6c8
-- title:
--   General-noise bad-part recursion (eqs. 8.8-8.10)
-- statement:
--   In the general-noise analysis the contribution of the bad (non-sparse) fault paths inside an $r$-rectangle is controlled by a quantity $b_r$ — in the paper, the norm $\|L_b^{r}(i)\|$ of the bad part of the fault-path expansion — which satisfies, by the same counting as in the probabilistic case,
--
--   $$b_{r+1} \;\le\; \binom{A}{k+1}\, b_r^{\,k+1}\,(1+b_r)^{A-k-1},$$
--
--   the extra factor coming from the good sub-rectangles, whose operators have norm at most $1+b_r$ rather than $1$.
--
--   The assertion is the resulting bound: if $2\eta A\le1$, if $\delta>0$ satisfies the gap condition $e\binom{A}{k+1}(2\eta)^{k+1}<(2\eta)^{1+\delta}$ of equation 8.9, and if a nonnegative sequence $(b_r)$ starts at $b_0\le2\eta$ and obeys the displayed recursion, then
--
--   $$b_r \;\le\; (2\eta)^{(1+\delta)^{r}} \qquad\text{for all } r,$$
--
--   which is equation 8.8. The hypothesis $2\eta A\le1$ is what allows $(1+b_r)^{A-k-1}$ to be bounded by $e$.
--
--   **Formalization Note** The statement is about an arbitrary real sequence satisfying the recursion, so it can be applied to the operator norms of the paper once a model of super-operators is available, without committing this mission to such a model.
-- source:
--   Dorit Aharonov and Michael Ben-Or, Fault-Tolerant Quantum Computation With Constant Error Rate, arXiv:quant-ph/9906129v1, https://arxiv.org/abs/quant-ph/9906129, pp. 53-54, proof of Lemma 11, eqs. (8.8), (8.9), (8.10)

import Definitions.Def_ABOThreshold_model

namespace ABOThreshold

theorem bad_norm_recursion (A k : ℕ) (hA : k + 1 ≤ A) (η δ : ℝ) (hη : 0 < η)
    (hηA : 2 * η * (A : ℝ) ≤ 1) (hδ : 0 < δ)
    (hthr : Real.exp 1 * (A.choose (k + 1) : ℝ) * (2 * η) ^ (k + 1) < (2 * η) ^ (1 + δ))
    (b : ℕ → ℝ) (hb0 : ∀ r, 0 ≤ b r) (hbase : b 0 ≤ 2 * η)
    (hstep : ∀ r, b (r + 1) ≤
      (A.choose (k + 1) : ℝ) * b r ^ (k + 1) * (1 + b r) ^ (A - k - 1)) :
    ∀ r : ℕ, b r ≤ (2 * η) ^ ((1 + δ) ^ r) := by sorry

end ABOThreshold
