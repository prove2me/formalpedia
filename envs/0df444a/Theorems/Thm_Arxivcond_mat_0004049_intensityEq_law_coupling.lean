-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_intensityEq_law_coupling
-- name    : Arxivcond_mat_0004049.intensityEq_law_coupling
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T15:27:38.023996+00:00
-- url     : https://prove2.me/theorems/9ca2ee04-3355-48c2-9bf2-d5ab31c04b39
-- title:
--   For $n=m$, $N I$ has the law of $|n^{-1/2}\sum z_k^2|^2 / (\frac1N\sum|z_k|^2)^2$ for i.i.d. complex Gaussians $z_k$
-- statement:
--   Let $\gamma > 0$ and $N \ge 1$. In the localized-regime model, the rescaled intensity $N I$ for equal incident and detected modes, $I = |C_0|^2$ with $C_0 = \sum_{i=1}^N u_i^2$ and $u = g/\|g\|_2$, has the same law as
--
--   $$
--   \frac{\Big|\frac{1}{\sqrt N}\sum_{k=0}^{N-1} z_k^2\Big|^2}{\Big(\frac1N \sum_{k=0}^{N-1} |z_k|^2\Big)^2},
--   $$
--
--   where $z_0, z_1, \dots$ are independent standard circular complex Gaussians ($\mathbb{E}|z_k|^2 = 1$).
--
--   The identity comes from $g = z/\sqrt N$ in law, which gives $C_0 = \sum_i g_i^2 / \sum_j |g_j|^2$. It places the laws of all $N$ on one probability space, so that the large-$N$ limit of $N I$ can be taken with a central limit theorem for the numerator and the law of large numbers for the denominator.
--
--   **Formalization Note** The common probability space is `Measure.infinitePi` of the complex Gaussian with independent $N(0, \tfrac12)$ parts. Both sides are $0$ on the null event $g = 0$, by Lean's convention $x/0 = 0$.
-- source:
--   H. Schomerus, K. J. H. van Bemmel, C. W. J. Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), https://arxiv.org/abs/cond-mat/0004049, p. 1, eq. (1), case $n = m$; p. 2, model of the eigenvector columns

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem intensityEq_law_coupling (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : 1 ≤ N) :
    (localizedModel N γ).map (fun ω => (N : ℝ) * intensityEq ω) =
      (Measure.infinitePi fun _ : ℕ => ((gaussianReal 0 (1 / 2)).prod
          (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm).map
        (fun z => Complex.normSq (((Real.sqrt N)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, z k ^ 2) /
          ((∑ k ∈ Finset.range N, Complex.normSq (z k)) / N) ^ 2) := by sorry

end Arxivcond_mat_0004049
