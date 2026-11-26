-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_clt_sum_sq_circular_gaussian
-- name    : Arxivcond_mat_0004049.clt_sum_sq_circular_gaussian
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T15:27:15.145836+00:00
-- url     : https://prove2.me/theorems/941e4d27-2d8b-52d3-a8aa-1644c229085a
-- title:
--   CLT for squares of circular complex Gaussians: $n^{-1/2}\sum_{k<n} z_k^2 \Rightarrow$ complex Gaussian with $N(0,1)$ parts
-- statement:
--   Let $z_0, z_1, \dots$ be independent standard circular complex Gaussians: $z_k = x_k + i y_k$ with $x_k, y_k$ independent $N(0, \tfrac12)$, so $\mathbb{E}|z_k|^2 = 1$. Then
--
--   $$
--   \frac{1}{\sqrt n} \sum_{k=0}^{n-1} z_k^2 \ \xrightarrow{\ d\ }\ W = A + iB, \qquad A, B \text{ independent } N(0, 1),
--   $$
--
--   as $n \to \infty$: for every bounded continuous $f : \mathbb{C} \to \mathbb{R}$, $\mathbb{E} f\big(n^{-1/2}\sum_{k<n} z_k^2\big) \to \mathbb{E} f(W)$.
--
--   The summands $z_k^2 = (x_k^2 - y_k^2) + 2i\,x_k y_k$ are i.i.d., centered, with uncorrelated real and imaginary parts of variance $1$ each. In the paper this is the large-$N$ behaviour of $C_0 = \sum_i u_i^2$ for equal incident and detected modes, which produces the factor $2$ in Rayleigh's law, eq. (1).
--
--   **Formalization Note** The i.i.d. sequence is the product measure `Measure.infinitePi` on $\mathbb{C}^{\mathbb{N}}$, and convergence in distribution is stated through bounded continuous test functions.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 1, eq. (1), case $n = m$ (large-$N$ limit of $C_0 = \sum_i u_i^2$)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem clt_sum_sq_circular_gaussian (f : BoundedContinuousFunction ℂ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, f (((Real.sqrt n)⁻¹ : ℂ) * ∑ k ∈ Finset.range n, z k ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => ((gaussianReal 0 (1 / 2)).prod
          (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm))
      atTop (𝓝 (∫ w, f w ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        Complex.measurableEquivRealProd.symm))) := by sorry

end Arxivcond_mat_0004049
