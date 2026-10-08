-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_feature_split_duals_agree
-- name    : BoydADMM.ModelFit.feature_split_duals_agree
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:36:57.003551+00:00
-- url     : https://prove2.me/theorems/98125a41-d796-4cbf-9823-6e121fa46006
-- title:
--   §8.3, p. 68 — feature splitting: the z-update reduces to the z̄-update and all duals equal Ax̄^{k+1} + ū^k − z̄^{k+1}
-- statement:
--   Consider the model-fitting problem split across features: the feature matrix is partitioned by columns as $A=[A_1\cdots A_N]$ with $A_i\in\mathbb R^{m\times n_i}$, $N\ge1$, the loss $l:\mathbb R^m\to\mathbb R$ is convex, $b\in\mathbb R^m$ and $\rho>0$. Fix the new local variables $x_i=x_i^{k+1}\in\mathbb R^{n_i}$ and the scaled duals $u_i=u_i^k\in\mathbb R^m$, and write
--   $$\overline{Ax}=\frac1N\sum_{i=1}^N A_ix_i,\qquad \bar u=\frac1N\sum_{i=1}^N u_i .$$
--   The $z$-update of the scaled ADMM minimizes over $(z_1,\dots,z_N)\in(\mathbb R^m)^N$
--   $$\Phi(z_1,\dots,z_N)=l\Bigl(\sum_{i=1}^N z_i-b\Bigr)+\sum_{i=1}^N\frac{\rho}{2}\|A_ix_i-z_i+u_i\|_2^2 .$$
--   For any $(z_1,\dots,z_N)$, with average $\bar z=\frac1N\sum_i z_i$:
--
--   1. $(z_1,\dots,z_N)$ minimizes $\Phi$ if and only if $\bar z$ minimizes
--   $$\bar z\mapsto l(N\bar z-b)+\frac{N\rho}{2}\|\bar z-\overline{Ax}-\bar u\|_2^2$$
--   and, for every $i$, $z_i=\bar z+A_ix_i+u_i-\overline{Ax}-\bar u$;
--   2. if $(z_1,\dots,z_N)$ minimizes $\Phi$, then the dual updates $u_i^{+}=u_i+A_ix_i-z_i$ all coincide:
--   $$u_i^{+}=\overline{Ax}+\bar u-\bar z\qquad\text{for every } i .$$
--
--   This is the reduction that turns the $N$-block $z$-update into a single problem in $m$ variables and lets the algorithm keep a single dual variable, as in the sharing problem.
--
--   **Formalization Note** The loss is real valued and convex, as in (8.1) on p. 61 ("$l:\mathbf R^m\to\mathbf R$ is a convex loss function"). The book introduces $\bar z^{k+1}$ as a minimizer and then defines $z_i^{k+1}$ from it; the statement formalizes this as the equivalence in item 1, with $\bar z$ the average of the $z_i$, so it says both that the two-step recipe produces a minimizer and that every minimizer arises this way. The book overlines the whole product, $\overline{Ax}^{k+1}$; it is a single vector, the average of the partial predictors. Iteration superscripts are dropped. The blocks are indexed by `Fin N`, i.e. from $0$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), pp. 67–68, §8.3

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.3, p. 68: in the feature-split ADMM, the `z`-update over `(z₁, …, z_N)` reduces to the
`z̄`-update for the average `z̄` plus the explicit formula for each `zᵢ`, and then all the scaled
dual variables `uᵢ^{k+1} = uᵢ^k + Aᵢxᵢ^{k+1} − zᵢ^{k+1}` equal `Ax̄^{k+1} + ū^k − z̄^{k+1}`. -/
theorem feature_split_duals_agree {N m : ℕ} {n : Fin N → ℕ} (hN : 0 < N)
    (A : ∀ i, Matrix (Fin m) (Fin (n i)) ℝ) (l : EuclideanSpace ℝ (Fin m) → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (b : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : ∀ i, EuclideanSpace ℝ (Fin (n i))) (u z u' : Fin N → EuclideanSpace ℝ (Fin m))
    (hu' : ∀ i, u' i = u i + Matrix.toEuclideanLin (A i) (x i) - z i) :
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z ↔
      (IsMinOn (fun zb : EuclideanSpace ℝ (Fin m) =>
          l ((N : ℝ) • zb - b) + (N : ℝ) * ρ / 2 *
            ‖zb - (N : ℝ)⁻¹ • (∑ i, Matrix.toEuclideanLin (A i) (x i))
              - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2)
          Set.univ ((N : ℝ)⁻¹ • (∑ i, z i)) ∧
        ∀ i, z i = (N : ℝ)⁻¹ • (∑ j, z j) + Matrix.toEuclideanLin (A i) (x i) + u i
          - (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
          - (N : ℝ)⁻¹ • (∑ j, u j))) ∧
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z →
      ∀ i, u' i = (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
        + (N : ℝ)⁻¹ • (∑ j, u j) - (N : ℝ)⁻¹ • (∑ j, z j)) := by sorry

end BoydADMM.ModelFit
