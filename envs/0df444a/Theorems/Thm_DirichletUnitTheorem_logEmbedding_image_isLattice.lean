-- Prove2me | Theorems.Thm_DirichletUnitTheorem_logEmbedding_image_isLattice
-- name    : DirichletUnitTheorem.logEmbedding_image_isLattice
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:02.932994+00:00
-- url     : https://prove2.me/theorems/86702f87-d49b-4e60-9e17-bbd3d11ad52f
-- title:
--   The logarithmic image of the units is a lattice in the trace-zero hyperplane
-- statement:
--   Let $K$ be a number field and consider the map $\ell:\mathcal O_K^\times\to\mathbb R^{r+1}$, indexed by the $r+1=r_1+r_2$ infinite places, given by
--
--   $$\ell(u) = \big(N_w\log\lvert u\rvert_w\big)_w.$$
--
--   Its image lies in the hyperplane $H=\{x : \sum_w x_w = 0\}$ and is a lattice there: it is a discrete subset of $\mathbb R^{r+1}$ and its $\mathbb R$-linear span is exactly $H$.
--
--   **Formalization Note** "Lattice in $H$" is encoded as: the image is discrete in the subspace topology and its real span equals $H$.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator", geometric interpretation ("has an image in the r-dimensional subspace ... consisting of all vectors whose entries have sum 0, and by Dirichlet's unit theorem the image is a lattice in this subspace").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem logEmbedding_image_isLattice (K : Type*) [Field K] [NumberField K] :
    DiscreteTopology (Set.range fun (u : (𝓞 K)ˣ) (w : InfinitePlace K) =>
        (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K))) ∧
      (Submodule.span ℝ (Set.range fun (u : (𝓞 K)ˣ) (w : InfinitePlace K) =>
          (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K))) : Set (InfinitePlace K → ℝ)) =
        {x | ∑ w, x w = 0} := by sorry

end DirichletUnitTheorem
