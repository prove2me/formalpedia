-- Prove2me | Theorems.Thm_EffResSparsify_Sampling_lemma_5
-- name    : EffResSparsify.Sampling.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:33:33.718564+00:00
-- url     : https://prove2.me/theorems/86a62e7e-4beb-4dc6-aa51-c02752a2db17
-- title:
--   Lemma 5 (Rudelson–Vershynin) — $\mathbb E\|\tfrac1q\sum y_iy_i^{\mathsf T}-\mathbb E yy^{\mathsf T}\|_2\le CM\sqrt{\log q/q}$ when this is $<1$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $d\ge0$, and let $y$ be a random vector in $\mathbb R^d$ taking finitely many values $y_i$ with probabilities $p_i\ge0$, $\sum_i p_i=1$. Suppose $\|y_i\|_2\le M$ whenever $p_i>0$, and $\|\mathbb E\,yy^{\mathsf T}\|_2\le1$, where $\mathbb E\,yy^{\mathsf T}=\sum_i p_i\,y_iy_i^{\mathsf T}$ and $\|\cdot\|_2$ is the spectral norm. Let $y_1,\dots,y_q$ be independent copies of $y$, with $q\ge2$, and put
--   $$a=CM\sqrt{\frac{\log q}{q}}.$$
--   If $a<1$, then
--   $$\mathbb E\,\Big\|\frac1q\sum_{j=1}^q y_jy_j^{\mathsf T}-\mathbb E\,yy^{\mathsf T}\Big\|_2\le a.$$
--
--   This is the matrix law of large numbers for sums of independent rank-one matrices on which the proof of Theorem 1 rests: applied to the rescaled columns of $\Pi$, it bounds the expected spectral distance between $\Pi S\Pi$ and $\Pi$.
--
--   **Formalization Note** The paper prints the conclusion as $\le\min(CM\sqrt{\log q/q},1)$ without the condition $a<1$. That form is false: at $q=1$ the right side is $0$ while the left side is positive for any nondegenerate distribution, and the bound $1$ also fails (for $d=1$, $y=M$ with probability $1/M^2$ and $0$ otherwise, $q=2$, $M^2=100$, the left side is about $1.96$). The statement here is the form of Rudelson and Vershynin's Theorem 3.1 (J. ACM 54 (2007)), with $q\ge2$ and the hypothesis $a<1$; Theorem 1 uses it only with $a\le\varepsilon/2<1$. The distribution is restricted to finite support (all Theorem 1 needs: the $m$ rescaled columns of $\Pi$); the expectation over the $q$ samples is the finite sum over $q$-tuples of indices weighted by $\prod_j p_{s_j}$. $\|y_i\|_2$ is the Euclidean norm $\sqrt{\sum_k y_i(k)^2}$, $\log$ is natural, and $C$ is quantified before $d$, the distribution, $M$ and $q$.
-- source:
--   Spielman, Srivastava, Graph Sparsification by Effective Resistances, arXiv:0803.0929v4, p. 8, Lemma 5 (citing Rudelson & Vershynin, Sampling from large matrices: an approach through geometric functional analysis, J. ACM 54(4), 2007, Thm. 3.1)

import Mathlib

namespace EffResSparsify.Sampling

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Lemma 5 (Rudelson–Vershynin [22], Thm. 3.1), p. 8, for a finitely supported distribution,
in Rudelson–Vershynin's form: there is an absolute constant `C > 0` such that, for every
distribution `p` on finitely many vectors `y_i ∈ ℝᵈ` with `‖y_i‖₂ ≤ M` on the support of `p` and
`‖E yyᵀ‖₂ ≤ 1`, and every `q ≥ 2` with `a := C M √(log q / q) < 1`, the expected spectral-norm
deviation of the empirical second-moment matrix of `q` independent samples satisfies
`E ‖(1/q) ∑_j y_j y_jᵀ − E yyᵀ‖₂ ≤ a`. The expectation is the finite sum over the `q`-tuples
`s` of indices, weighted by `∏_j p_{s j}`. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (ι : Type) [Fintype ι] (p : ι → ℝ) (y : ι → Fin d → ℝ) (M : ℝ),
        (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        (∀ i, 0 < p i → Real.sqrt (∑ k, y i k ^ 2) ≤ M) →
        ‖∑ i, p i • vecMulVec (y i) (y i)‖ ≤ 1 →
        ∀ q : ℕ, 2 ≤ q → C * M * Real.sqrt (Real.log q / q) < 1 →
          ∑ s : Fin q → ι, (∏ j, p (s j)) *
              ‖(1 / (q : ℝ)) • ∑ j, vecMulVec (y (s j)) (y (s j)) -
                ∑ i, p i • vecMulVec (y i) (y i)‖ ≤
            C * M * Real.sqrt (Real.log q / q) := by sorry

end EffResSparsify.Sampling
