-- Prove2me | Theorems.Thm_AdamDyn_DecConv_lemma_9_1
-- name    : AdamDyn.DecConv.lemma_9_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:57.796819+00:00
-- url     : https://prove2.me/theorems/fbe7af87-1d22-4156-bac5-57a450b2901e
-- title:
--   Lemma 9.1 i)–ii) — r_n = 1 − ∏α_i, nondecreasing, converging to 1
-- statement:
--   Let $(\alpha_n)$ and $(\gamma_n)$ be real sequences with $0\le\alpha_n\le1$ and $\gamma_n>0$ for all $n$, $\sum_n\gamma_n=+\infty$, and $(1-\alpha_n)/\gamma_n\to a$ for some $a>0$. Let $r_0=0$ and $r_n=\alpha_nr_{n-1}+(1-\alpha_n)$ for $n\ge1$ (the bias-correction weights of Algorithm 5.1). Then
--
--   1. for every $n\in\mathbb N$, $$r_n=1-\prod_{i=1}^n\alpha_i;$$
--   2. the sequence $(r_n)$ is nondecreasing and converges to $1$.
--
--   The same statement applied to $(\beta_n)$ (with limit $b>0$) gives the corresponding facts for $\bar r_n$ ("a similar lemma holds for the sequence $(\bar r_n)$"). These facts make the bias-corrected moments $\hat m_n=m_n/r_n$, $\hat v_n=v_n/\bar r_n$ asymptotically equal to $m_n$, $v_n$.
--
--   **Formalization Note** The page assumes only $0\le\alpha_n\le1$ and $(1-\alpha_n)/\gamma_n\to a>0$; the convergence $r_n\to1$ also needs $\gamma_n>0$ and $\sum_n\gamma_n=+\infty$ (Assumption 5.1 i)–ii), in force wherever the lemma is used), which are added. Point iii) of the lemma concerns Theorem 5.7 and is not stated. The empty product ($n=0$) is $1$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 25, Lemma 9.1 i)–ii)

import Mathlib
import Definitions.Def_AdamDyn_DecConv_Algorithm

open Filter Topology

namespace AdamDyn.DecConv

/-- Lemma 9.1 i)–ii) (Barakat & Bianchi, arXiv:1810.02263v4, p. 25). For `α` with values in
`[0, 1]`, `(1 - α_n)/γ_n → a > 0`, `γ_n > 0` and `Σ γ_n = +∞`, the bias-correction weights of
Algorithm 5.1 satisfy `r_n = 1 - ∏_{i=1}^n α_i`, are nondecreasing, and converge to `1`.
Applied to `β` it gives the same for `r̄_n`. -/
theorem lemma_9_1 (γ α : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 1)
    (hlim : Tendsto (fun n => (1 - α n) / γ n) atTop (𝓝 a))
    (hγ : ∀ n, 0 < γ n)
    (hsum : Tendsto (fun N => ∑ n ∈ Finset.range N, γ n) atTop atTop) :
    (∀ n, biasWeight α n = 1 - ∏ i ∈ Finset.Icc 1 n, α i) ∧
      Monotone (biasWeight α) ∧ Tendsto (biasWeight α) atTop (𝓝 1) := by sorry

end AdamDyn.DecConv
