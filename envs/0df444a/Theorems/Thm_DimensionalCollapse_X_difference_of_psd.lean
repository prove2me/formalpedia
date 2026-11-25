-- Prove2me | Theorems.Thm_DimensionalCollapse_X_difference_of_psd
-- name    : DimensionalCollapse.X_difference_of_psd
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:53:02.711668+00:00
-- url     : https://prove2.me/theorems/165b81fd-c60e-4da0-8517-c75e81545cda
-- title:
--   Lemma 2: $X=\hat\Sigma_0-\hat\Sigma_1$ is a difference of two PSD matrices
-- statement:
--   For inputs $x_i,x_i'\in\mathbb{R}^n$ and any linear model $W\in\mathbb{R}^{d\times n}$, with the softmax weights $\alpha_{ij}$ computed from $z=Wx$, $z'=Wx'$, the matrix $X$ is a difference of two positive semidefinite matrices:
--   $$X=\hat\Sigma_0-\hat\Sigma_1,\qquad \hat\Sigma_0=\sum_{i,j}\alpha_{ij}(x_i-x_j)(x_i-x_j)^\top\succeq0,\qquad \hat\Sigma_1=\sum_i(1-\alpha_{ii})(x_i'-x_i)(x_i'-x_i)^\top\succeq0 .$$
--
--   Here $\hat\Sigma_0$ is a weighted covariance of the data and $\hat\Sigma_1$ a weighted covariance of the augmentation, so the strength of the augmentation decides whether $X$ is positive definite.
--
--   **Formalization Note** $X$ is taken in the form of Appendix B.2; see the note on eqs. (4)–(5).
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 4.2, Lemma 2, eq. (7), p. 4; proof in Appendix B.2, p. 14

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem X_difference_of_psd {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : Matrix (Fin d) (Fin n) ℝ) :
    Xmat x x' W = Sigma0 x x' W - Sigma1 x x' W ∧
      (Sigma0 x x' W).PosSemidef ∧ (Sigma1 x x' W).PosSemidef := by sorry

end DimensionalCollapse
