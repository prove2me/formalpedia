-- Prove2me | Theorems.Thm_DimensionalCollapse_two_layer_singular_value_dynamics
-- name    : DimensionalCollapse.two_layer_singular_value_dynamics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:55:25.330037+00:00
-- url     : https://prove2.me/theorems/42c79513-b20d-4427-8beb-d57f3faca79a
-- title:
--   Lemma 7: singular value dynamics of the two-layer model
-- statement:
--   Let $W_1,W_2$ follow the two-layer InfoNCE gradient flow at time $t$ (as in Lemma 3), and let $W_l(s)=U_l(s)\,\mathrm{diag}(\sigma_l(s))\,V_l(s)^\top$ ($l=1,2$) be singular value decompositions for $s$ near $t$, with $U_l,V_l,\sigma_l$ differentiable at $t$. Write $u_l^k,v_l^k$ for the $k$-th columns of $U_l(t),V_l(t)$ and $G$ for the matrix of Lemma 1 at $z=W_2(t)W_1(t)x$. Then for every $k$
--   $$\dot\sigma_1^k=-\sum_{k'}\big(v_2^{k'\top}u_1^k\big)\,\sigma_2^{k'}\,\big(u_2^{k'\top}Gv_1^k\big),\qquad \dot\sigma_2^k=-\sum_{k'}\big(u_1^{k'\top}v_2^k\big)\,\sigma_1^{k'}\,\big(u_2^{k\top}Gv_1^{k'}\big).$$
--
--   The overlaps $v_2^{k'\top}u_1^k$ are the entries of the alignment matrix $A=V_2^\top U_1$; when $A=I$ the sums collapse to one term, which gives Theorem 3.
--
--   **Formalization Note** The differentiable SVDs are hypotheses on a neighbourhood of $t$, as in Lemma 4.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Appendix A, Lemma 7, eqs. (21)–(22), p. 13

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem two_layer_singular_value_dynamics {N d : ℕ} (x x' : Fin N → Fin d → ℝ)
    (W1 W2 U1 V1 U2 V2 : ℝ → Matrix (Fin d) (Fin d) ℝ) (sig1 sig2 : ℝ → Fin d → ℝ) (t : ℝ)
    (hflow : IsTwoLayerFlowAt x x' W1 W2 t)
    (hsvd1 : IsDiffSVDAt W1 U1 V1 sig1 t) (hsvd2 : IsDiffSVDAt W2 U2 V2 sig2 t) :
    (∀ k, deriv (fun s => sig1 s k) t =
      -∑ k', (∑ a, V2 t a k' * U1 t a k) * sig2 t k' *
        (∑ a, ∑ b, U2 t a k' * Gmat x x' (W2 t * W1 t) a b * V1 t b k)) ∧
    (∀ k, deriv (fun s => sig2 s k) t =
      -∑ k', (∑ a, U1 t a k' * V2 t a k) * sig1 t k' *
        (∑ a, ∑ b, U2 t a k * Gmat x x' (W2 t * W1 t) a b * V1 t b k')) := by sorry

end DimensionalCollapse
