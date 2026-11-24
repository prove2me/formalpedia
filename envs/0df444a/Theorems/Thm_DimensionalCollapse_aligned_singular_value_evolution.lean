-- Prove2me | Theorems.Thm_DimensionalCollapse_aligned_singular_value_evolution
-- name    : DimensionalCollapse.aligned_singular_value_evolution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:56:02.525101+00:00
-- url     : https://prove2.me/theorems/237dd63b-8d1a-4692-a8ec-cdde60270143
-- title:
--   Theorem 3 (as proved): singular values of aligned weights under InfoNCE
-- statement:
--   Let $W_1,W_2\in\mathbb{R}^{d\times d}$ follow the two-layer InfoNCE gradient flow at time $t$, with differentiable singular value decompositions $W_l(s)=U_l(s)\,\mathrm{diag}(\sigma_l(s))\,V_l(s)^\top$ for $s$ near $t$, as in Lemma 7. If $W_2$ and $W_1$ are aligned at time $t$, that is $V_2(t)=U_1(t)$, then for every $k$
--   $$\dot\sigma_1^k=\sigma_1^k\,(\sigma_2^k)^2\,\big(v_1^{k\top}Xv_1^k\big),\qquad \dot\sigma_2^k=\sigma_2^k\,(\sigma_1^k)^2\,\big(v_1^{k\top}Xv_1^k\big),$$
--   where $v_1^k$ is the $k$-th column of $V_1(t)$ and $X$ is the matrix of eq. (6) computed from the embeddings $z=W_2(t)W_1(t)x$.
--
--   When $X$ is positive definite, each pair of singular values grows at a rate proportional to itself, so the smallest singular values grow much more slowly than the others; this is the implicit-regularization mechanism of dimensional collapse.
--
--   **Formalization Note** The paper writes the alignment as "$V_2=U_1^\top$"; alignment is defined in Section 5.3 as $A=V_2^\top U_1=I$, i.e. $V_2=U_1$, which is what the proof uses, so the hypothesis is $V_2(t)=U_1(t)$. The paper's proof takes alignment as a limit ("$\to$"); here alignment holds exactly at time $t$ and the identities are exact. $X$ is in the form of Appendix B.2.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Section 5.3, Theorem 3, eq. (10), p. 6; proof in Appendix B.6, p. 15

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem aligned_singular_value_evolution {N d : ℕ} (x x' : Fin N → Fin d → ℝ)
    (W1 W2 U1 V1 U2 V2 : ℝ → Matrix (Fin d) (Fin d) ℝ) (sig1 sig2 : ℝ → Fin d → ℝ) (t : ℝ)
    (hflow : IsTwoLayerFlowAt x x' W1 W2 t)
    (hsvd1 : IsDiffSVDAt W1 U1 V1 sig1 t) (hsvd2 : IsDiffSVDAt W2 U2 V2 sig2 t)
    (halign : V2 t = U1 t) :
    ∀ k,
      deriv (fun s => sig1 s k) t = sig1 t k * sig2 t k ^ 2 *
        (∑ a, ∑ b, V1 t a k * Xmat x x' (W2 t * W1 t) a b * V1 t b k) ∧
      deriv (fun s => sig2 s k) t = sig2 t k * sig1 t k ^ 2 *
        (∑ a, ∑ b, V1 t a k * Xmat x x' (W2 t * W1 t) a b * V1 t b k) := by sorry

end DimensionalCollapse
