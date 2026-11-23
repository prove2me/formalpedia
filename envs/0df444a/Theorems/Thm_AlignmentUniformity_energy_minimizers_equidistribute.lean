-- Prove2me | Theorems.Thm_AlignmentUniformity_energy_minimizers_equidistribute
-- name    : AlignmentUniformity.energy_minimizers_equidistribute
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:29:21.067398+00:00
-- url     : https://prove2.me/theorems/b4724234-3f61-4f36-b51c-ae48347b4da5
-- title:
--   Proposition 2: $N$-point minimizers converge weak* to $\sigma_d$
-- statement:
--   Let $d\ge0$ and $t>0$. For each $N\ge1$, let $\mathbf{u}^*_N=(u^*_{N,1},\dots,u^*_{N,N})$ be an $N$-point minimizer of the pairwise potential:
--
--   $$\mathbf{u}^*_N\in\operatorname*{argmin}_{u_1,\dots,u_N\in S^d}\ \sum_{1\le i<j\le N}G_t(u_i,u_j).$$
--
--   Then the normalized counting measures $\frac1N\sum_{i=1}^N\delta_{u^*_{N,i}}$ converge weak\* to $\sigma_d$ as $N\to\infty$: for every continuous $f:\mathbb{R}^{d+1}\to\mathbb{R}$,
--
--   $$\lim_{N\to\infty}\frac1N\sum_{i=1}^Nf(u^*_{N,i})=\int f\,d\sigma_d.$$
--
--   This is the finite-sample counterpart of Proposition 1.
--
--   **Formalization Note** The minimizer need not be unique. The statement holds for every choice of minimizers, as in the paper's Lemma 2 ("any energy minimizing sequence").
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Section 4.1.2, Proposition 2, p. 5; restated in Appendix A.1, Proposition 2, p. 15

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem energy_minimizers_equidistribute (d : ℕ) {t : ℝ} (ht : 0 < t)
    (u : (N : ℕ) → Fin N → Vec (d + 1))
    (hu : ∀ N : ℕ, 0 < N →
      (∀ i, u N i ∈ Metric.sphere (0 : Vec (d + 1)) 1) ∧
        ∀ v : Fin N → Vec (d + 1), (∀ i, v i ∈ Metric.sphere (0 : Vec (d + 1)) 1) →
          pairPotential t (u N) ≤ pairPotential t v) :
    WeakStarTendsto (fun N => normCounting (u N)) (sphereUnif (d + 1)) := by sorry

end AlignmentUniformity
