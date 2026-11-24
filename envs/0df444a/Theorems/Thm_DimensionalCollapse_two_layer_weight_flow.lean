-- Prove2me | Theorems.Thm_DimensionalCollapse_two_layer_weight_flow
-- name    : DimensionalCollapse.two_layer_weight_flow
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:54:37.383027+00:00
-- url     : https://prove2.me/theorems/535522d5-e9f9-43e3-9187-3139d31fb0b5
-- title:
--   Lemma 3: the weights of the two-layer model evolve by $\dot W_1=-W_2^TG$, $\dot W_2=-GW_1^T$
-- statement:
--   Let $(x_i,x_i')_{i=1}^N$ be inputs in $\mathbb{R}^d$, and let $W_1(t),W_2(t)\in\mathbb{R}^{d\times d}$ be the weights of the two-layer linear model $z=W_2W_1x$. If at time $t$ the weights follow the gradient flow of the InfoNCE loss,
--   $$\dot W_1=-\frac{\partial L}{\partial W_1},\qquad \dot W_2=-\frac{\partial L}{\partial W_2},$$
--   then
--   $$\dot W_1=-W_2^\top G,\qquad \dot W_2=-GW_1^\top,$$
--   where $G=\sum_i(g_{z_i}x_i^\top+g_{z_i'}x_i'^\top)$ is evaluated at the embeddings $z=W_2W_1x$, $z'=W_2W_1x'$.
--
--   Together with eq. (9), $G=-W_2W_1X$, this gives the dynamics studied in Section 5.
--
--   **Formalization Note** Derivatives in time are entrywise, and the hypothesis is required only at the time $t$.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 5.2, Lemma 3, eq. (8), p. 5, and eq. (9), p. 5; proof in Appendix B.4, p. 14

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem two_layer_weight_flow {N d : ℕ} (x x' : Fin N → Fin d → ℝ)
    (W1 W2 : ℝ → Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (hflow : IsTwoLayerFlowAt x x' W1 W2 t) :
    (∀ a b, HasDerivAt (fun s => W1 s a b) (-((W2 t)ᵀ * Gmat x x' (W2 t * W1 t)) a b) t) ∧
    (∀ a b, HasDerivAt (fun s => W2 s a b) (-(Gmat x x' (W2 t * W1 t) * (W1 t)ᵀ) a b) t) := by sorry

end DimensionalCollapse
