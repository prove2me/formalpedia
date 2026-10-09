-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_infconv_imp_dr
-- name    : DRConvexOpt.InfConv.infconv_imp_dr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:51.086632+00:00
-- url     : https://prove2.me/theorems/d345c33c-086b-4a63-a8a0-a55c9da4e47e
-- title:
--   Proof of Theorem 3, p. 37 — the infimal convolution bound (7) implies the distributionally robust constraint (3)
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set, $\mathcal P^j$ its outer approximations for a partition $\{\mathcal I_j\}_{j\in\mathcal J}$, $v$ as in (C3), $x \in \mathbb R^N$ and $w \in \mathbb R$. If the infimal convolution bound (7) holds,
--   $$\inf_{(y,\delta)\in\Gamma(x)} \sum_{j\in\mathcal J}\delta_j \sup_{\mathbb P\in\mathcal P^j}\mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \le w,$$
--   then the distributionally robust constraint (3) holds: $\mathbb E_{\mathbb P}[v(x,\tilde z)] \le w$ for every $\mathbb P \in \mathcal P$.
--
--   This is the second implication in the chain of Theorem 3: (7) is a conservative approximation of (3).
--
--   **Formalization Note** The left side of (7) is an `EReal` infimum. Constraint (3) is stated in its $\forall$-form. No standing condition is needed: members of $\mathcal P$ have a finite first moment, so $v(x,\tilde z)$ is integrable.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 37, proof of Theorem 3, end of first paragraph

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proof of Theorem 3, p. 37: the infimal convolution bound (7) implies the distributionally robust
constraint (3). -/
theorem infconv_imp_dr {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (x : Fin nN → ℝ) (w : ℝ) :
    infConvBound d blk v x ≤ (w : EReal) →
      ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w := by sorry

end DRConvexOpt.InfConv
