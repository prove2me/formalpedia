-- Prove2me | Theorems.Thm_DimensionalCollapse_infonce_gradients_and_G_eq_neg_WX
-- name    : DimensionalCollapse.infonce_gradients_and_G_eq_neg_WX
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:52:24.97903+00:00
-- url     : https://prove2.me/theorems/60104116-b5bb-4d57-b0bb-cd7c5ee30424
-- title:
--   Eqs. (4)–(5) (as corrected): InfoNCE embedding gradients and $G=-WX$
-- statement:
--   For embeddings $z_i,z_i'\in\mathbb{R}^d$ ($i=1,\dots,N$), the gradients of the InfoNCE loss are
--   $$g_{z_i}=\sum_{j\neq i}\alpha_{ij}(z_j-z_i')+\sum_{j\neq i}\alpha_{ji}(z_j-z_i),\qquad g_{z_i'}=\sum_{j\neq i}\alpha_{ij}(z_i'-z_i).$$
--   Consequently, for every linear model $W\in\mathbb{R}^{d\times n}$ and inputs $x_i,x_i'\in\mathbb{R}^n$, with $z=Wx$,
--   $$G=\sum_i\big(g_{z_i}x_i^\top+g_{z_i'}x_i'^\top\big)=-WX,$$
--   where
--   $$X=\sum_i\Big(\sum_{j\neq i}\alpha_{ij}(x_i'-x_j)+\sum_{j\neq i}\alpha_{ji}(x_i-x_j)\Big)x_i^\top-\sum_i(1-\alpha_{ii})(x_i'-x_i)x_i'^\top .$$
--
--   Combined with Lemma 1, the linear model evolves by $\dot W=WX$, which is the equation that Theorem 1 studies.
--
--   **Formalization Note** The matrix $X$ is the one written at the start of the proof of Lemma 2 (Appendix B.2, p. 14). Eq. (6) on p. 4 prints a minus sign in front of the first sum; with that sign, $G=-WX$ is false (a numerical check with $N=4$, $n=d=3$ gives an error of order $1$).
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 4.2, eqs. (4), (5), (6), p. 4; X in the form of Appendix B.2, p. 14

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem infonce_gradients_and_G_eq_neg_WX {N n d : ℕ} :
    (∀ (z z' : Fin N → Fin d → ℝ) (i : Fin N),
      gradZ z z' i = (∑ j ∈ Finset.univ.erase i, alpha z z' i j • (z j - z' i)) +
        ∑ j ∈ Finset.univ.erase i, alpha z z' j i • (z j - z i)) ∧
    (∀ (z z' : Fin N → Fin d → ℝ) (i : Fin N),
      gradZ' z z' i = ∑ j ∈ Finset.univ.erase i, alpha z z' i j • (z' i - z i)) ∧
    (∀ (x x' : Fin N → Fin n → ℝ) (W : Matrix (Fin d) (Fin n) ℝ),
      Gmat x x' W = -(W * Xmat x x' W)) := by sorry

end DimensionalCollapse
