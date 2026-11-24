-- Prove2me | Theorems.Thm_DimensionalCollapse_singular_value_derivative
-- name    : DimensionalCollapse.singular_value_derivative
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:55:02.653692+00:00
-- url     : https://prove2.me/theorems/9c899c09-89c5-4417-b3b1-e086ec1a4944
-- title:
--   Lemma 4: singular values evolve by $\dot\sigma^k=u^{kT}\dot W v^k$
-- statement:
--   Let $W(s)\in\mathbb{R}^{d\times d}$ have, for all $s$ near $t$, a singular value decomposition $W(s)=U(s)\,\mathrm{diag}(\sigma^1(s),\dots,\sigma^d(s))\,V(s)^\top$ with $U(s),V(s)$ orthogonal and $\sigma^k(s)\ge0$, and suppose $U$, $V$ and the $\sigma^k$ are differentiable at $t$. Then for every $k$
--   $$\dot\sigma^k(t)=u^{k}(t)^\top\,\dot W(t)\,v^k(t),$$
--   where $u^k,v^k$ are the $k$-th columns of $U$ and $V$.
--
--   This is the singular-value part of the matrix-dynamics lemma of Arora et al. (2019).
--
--   **Formalization Note** The paper assumes a differentiable SVD implicitly; it is written as a hypothesis on a neighbourhood of $t$. The singular values are not required to be sorted or distinct, since the identity does not need it.
-- source:
--   Jing, Vincent, LeCun and Tian, Understanding Dimensional Collapse in Contrastive Self-supervised Learning, ICLR 2022, arXiv:2110.09348v3, Appendix A, Lemma 4, eq. (12), p. 11

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

open Matrix Filter Topology

namespace DimensionalCollapse

theorem singular_value_derivative {d : ℕ} (W U V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (sig : ℝ → Fin d → ℝ) (t : ℝ) (hsvd : IsDiffSVDAt W U V sig t) :
    ∀ k, deriv (fun s => sig s k) t =
      ∑ a, ∑ b, U t a k * deriv (fun s => W s a b) t * V t b k := by sorry

end DimensionalCollapse
