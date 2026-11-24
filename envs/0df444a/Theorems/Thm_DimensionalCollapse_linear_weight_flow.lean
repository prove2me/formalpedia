-- Prove2me | Theorems.Thm_DimensionalCollapse_linear_weight_flow
-- name    : DimensionalCollapse.linear_weight_flow
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:51:04.748288+00:00
-- url     : https://prove2.me/theorems/dadc86ce-ca9f-42d6-bbf7-44c8c5d06ce0
-- title:
--   Lemma 1: the weights of the linear model evolve by $\dot W=-G$
-- statement:
--   Let $(x_i,x_i')_{i=1}^N$ be inputs in $\mathbb{R}^n$, and let $W(t)\in\mathbb{R}^{d\times n}$ be the weight of the linear model $z=Wx$ trained on the InfoNCE loss $L(W)$ by gradient flow. If at time $t$
--   $$\dot W(t)=-\frac{\partial L}{\partial W}\big(W(t)\big),$$
--   then
--   $$\dot W(t)=-G,\qquad G=\sum_i\big(g_{z_i}x_i^\top+g_{z_i'}x_i'^\top\big),$$
--   where $g_{z_i},g_{z_i'}$ are the gradients of the loss with respect to the embeddings $z_i=W(t)x_i$, $z_i'=W(t)x_i'$.
--
--   This is the chain rule for the linear model, and it reduces the training dynamics to the gradients on the embeddings.
--
--   **Formalization Note** Derivatives in time are taken entrywise, and the hypothesis is required only at the time $t$ where the conclusion is drawn.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 4.2, Lemma 1, eq. (3), p. 4; proof in Appendix B.1, p. 13

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem linear_weight_flow {N n d : ℕ} (x x' : Fin N → Fin n → ℝ)
    (W : ℝ → Matrix (Fin d) (Fin n) ℝ) (t : ℝ)
    (hW : ∀ a b, HasDerivAt (fun s => W s a b) (-(matGrad (linLoss x x') (W t)) a b) t) :
    ∀ a b, HasDerivAt (fun s => W s a b) (-(Gmat x x' (W t)) a b) t := by sorry

end DimensionalCollapse
